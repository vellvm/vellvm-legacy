Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../Vellvm".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import vellvm.
Require Import Kildall.
Require Import ListSet.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import dtree.
Require Import primitives.
Require Import Maps.
Require Import mem2reg.
Require Import opsem_props.

Module Promotability.

Definition DGVMap := @Opsem.GVsMap DGVs.

Record PhiInfo := mkPhiInfo {
  PI_f: fdef;
  PI_rd: list l;
  PI_succs: ATree.t (list l);
  PI_preds: ATree.t (list l);
  PI_id: id;
  PI_typ: typ;
  PI_align: align;
  PI_newids: ATree.t (id*id*id)  
}.

Definition promotable_alloca (f:fdef) (pid:id) (ty:typ) (al:align) : Prop :=
match getEntryBlock f with
| Some (block_intro _ _ cs _) =>
    find_promotable_alloca f cs nil = Some (pid, ty, al)
| _ => False
end.

Definition WF_PhiInfo (pinfo: PhiInfo) : Prop :=
let '(mkPhiInfo f rd succs preds pid ty al newids) := pinfo in
promotable_alloca f pid ty al /\
reachablity_analysis f = Some rd /\
succs = successors f /\
preds = make_predecessors succs /\
newids = fst (gen_fresh_ids rd (getFdefLocs f)).

(* wf_global and wf_globals are copied from sb_ds_gv_inject.v 
   We should move the invariant to memory model. *)
Fixpoint wf_global (maxb:Values.block) (gv:GenericValue) 
  : Prop :=
match gv with
| nil => True
| (Vptr b _,_)::gv' => b <= maxb /\ wf_global maxb gv'
| _::gv' => wf_global maxb gv'
end.

Fixpoint wf_globals maxb (gl:GVMap) : Prop :=
match gl with
| nil => True
| (_,gv)::gl' => wf_global maxb gv /\ wf_globals maxb gl'
end.

Fixpoint no_alias_with_blk (gvs:GenericValue) (blk:Values.block) : Prop :=
match gvs with
| nil => True
| (Vptr b _,_)::gvs' => b <> blk /\ no_alias_with_blk gvs' blk
| _::gvs' => no_alias_with_blk gvs' blk
end.

Fixpoint no_alias (gvs1 gvs2:GenericValue) : Prop :=
match gvs2 with
| nil => True
| (Vptr b _,_)::gvs2' => no_alias_with_blk gvs1 b /\ no_alias gvs1 gvs2'
| _::gvs2' => no_alias gvs1 gvs2'
end.

Definition wf_non_alloca_GVs (pinfo:PhiInfo) (id1:id) (gvs1 gvsa:GenericValue) 
  : Prop :=
(if (id_dec id1 (PI_id pinfo)) then True else no_alias gvs1 gvsa).

Definition wf_alloca_GVs (maxb:Values.block) (pinfo:PhiInfo) TD Mem 
  (gvsa:GenericValue) (als:list Values.block) : Prop :=
(exists mb, gvsa = ($ (blk2GV TD mb) # (typ_pointer (PI_typ pinfo)) $) /\
   In mb als /\ maxb < mb) /\
(forall gptr gvs1 ty al, 
   mload TD Mem gptr ty al = Some gvs1 ->
   no_alias gvs1 gvsa) /\
exists gv,
  mload TD Mem gvsa (PI_typ pinfo) (PI_align pinfo) = Some gv.

Definition wf_defs (maxb:Values.block) (pinfo:PhiInfo) TD M (lc:DGVMap) 
  (ids0:list atom) (als:list Values.block) : Prop :=
forall gvsa
  (Hinp: In (PI_id pinfo) ids0)
  (Hlkp: lookupAL _ lc (PI_id pinfo) = Some gvsa),
  wf_alloca_GVs maxb pinfo TD M gvsa als /\
  (forall id0 gvs0 
   (Hin0: In id0 ids0) 
   (Hlk0: lookupAL _ lc id0 = Some gvs0),
   wf_non_alloca_GVs pinfo id0 gvs0 gvsa).

Definition mk_gptr (blk:Values.block) (ofs:int32) : GenericValue :=
((Vptr blk ofs, AST.Mint 31)::nil).

Definition wf_lc M lc : Prop :=
(forall id0 blk ofs, 
  lookupAL _ lc id0 = Some (mk_gptr blk ofs) -> blk < Mem.nextblock M).

(* Except domination property, the other properties are the same for a lot of 
   proofs, we should prove them all for once. Or, we do not need to use them
   in this invariant, we can assume the invariant in opsem_wf, which is 
   preserved *)
Definition wf_ExecutionContext (maxb:Values.block) (pinfo:PhiInfo) TD M 
  (ec:Opsem.ExecutionContext) : Prop :=
let '(Opsem.mkEC f b cs tmn lc als) := ec in
(if (fdef_dec (PI_f pinfo) f) then 
  match cs with
  | nil => 
    match inscope_of_tmn f b tmn with
    | Some ids => wf_defs maxb pinfo TD M lc ids als
    | None => False
    end
  | c::_ =>
    match inscope_of_cmd f b c with
    | Some ids => wf_defs maxb pinfo TD M lc ids als
    | None => False
    end
  end 
else True)
/\ wf_lc M lc.

Definition wf_ECStack_head_in_tail (maxb:Values.block) (pinfo:PhiInfo) TD M 
  (lc:DGVMap) (ec0:fdef * DGVMap) : Prop :=
forall gvsa,
  fst ec0 = PI_f pinfo ->
  lookupAL _ (snd ec0) (PI_id pinfo) = Some gvsa ->
  (exists mb, gvsa = ($ (blk2GV TD mb) # (typ_pointer (PI_typ pinfo)) $) /\ 
    maxb < mb < Mem.nextblock M) /\
  (forall id1 gvs1, 
    lookupAL _ lc id1 = Some gvs1 -> 
    no_alias gvs1 gvsa) /\
  (forall gptr t al gvs1, 
    mload TD M gptr t al = Some gvs1 -> 
    no_alias gvs1 gvsa).

Definition wf_ECStack_head_tail (maxb:Values.block) (pinfo:PhiInfo) TD M 
  (lc:DGVMap) (ecs':list (fdef * DGVMap)) : Prop :=
  forall ec0, In ec0 ecs' -> wf_ECStack_head_in_tail maxb pinfo TD M lc ec0.

Fixpoint wf_ECStack (maxb:Values.block) (pinfo:PhiInfo) TD M (ecs:Opsem.ECStack)
  : Prop :=
match ecs with
| nil => True
| ec::ecs' => 
    wf_ExecutionContext maxb pinfo TD M ec /\
    wf_ECStack maxb pinfo TD M ecs' /\
    wf_ECStack_head_tail maxb pinfo TD M (Opsem.Locals ec) 
      (List.map (fun ec => let '(Opsem.mkEC f _ _ _ lc _) := ec in (f, lc)) ecs')
end.

Definition wf_Mem maxb (td:targetdata) (M:mem) : Prop :=
(forall gptr ty al blk ofs, 
  mload td M gptr ty al = Some (mk_gptr blk ofs) -> blk < Mem.nextblock M) /\
maxb < Mem.nextblock M.

Definition wf_als maxb M (als: list Values.block) : Prop :=
NoDup als /\ (forall al, In al als -> maxb < al < Mem.nextblock M).

Definition wf_State (maxb:Values.block) (pinfo:PhiInfo) (cfg:OpsemAux.Config) 
  (S:Opsem.State) : Prop :=
let '(OpsemAux.mkCfg _ td _ _ _ ) := cfg in
let '(Opsem.mkState ecs M) := S in
wf_ECStack maxb pinfo td M ecs /\
wf_als maxb M 
  (flat_map (fun ec => let '(Opsem.mkEC _ _ _ _ _ als) := ec in als) ecs) /\
wf_Mem maxb td M.

Lemma wf_defs_eq : forall maxb pinfo TD M lc ids1 ids2 als,
  AtomSet.set_eq _ ids1 ids2 ->
  wf_defs maxb pinfo TD M lc ids1 als ->
  wf_defs maxb pinfo TD M lc ids2 als.
Proof.
  intros. unfold wf_defs in *. intros.
  destruct H as [H1 H2]. eauto.
  apply H0 in Hlkp; auto.
    destruct Hlkp as [J1 J2].
    split; auto.
Qed.

Definition wf_GVs (maxb:Values.block)(pinfo:PhiInfo)(TD:targetdata)(M:mem)
  (lc:DGVMap)(ids1:list id)(als:list Values.block)(id1:id)(gv1:GVsT DGVs)
  : Prop :=
  (forall gvsa,
     In (PI_id pinfo) ids1 ->
     lookupAL _ lc (PI_id pinfo) = Some gvsa ->
     no_alias gv1 gvsa) /\
  (id1 = (PI_id pinfo) ->
     (forall id0 gvs0,
        lookupAL (GVsT DGVs) lc id0 = ret gvs0 ->
        no_alias gvs0 gv1) /\
     wf_alloca_GVs maxb pinfo TD M gv1 als).

Lemma wf_defs_updateAddAL: forall maxb pinfo TD M lc' ids1 ids2 i1 gv1 als
  (HwfDef: wf_defs maxb pinfo TD M lc' ids1 als)
  (Heq: AtomSet.set_eq _ (i1::ids1) ids2)
  (Hwfgvs: wf_GVs maxb pinfo TD M lc' ids1 als i1 gv1),
  wf_defs maxb pinfo TD M (updateAddAL _ lc' i1 gv1) ids2 als.
Proof.
  intros. unfold wf_defs. intros.
  destruct Hwfgvs as [Hwfgvs1 Hwfgvs2].
  destruct Heq as [Hinc1 Hinc2].
  apply Hinc2 in Hinp. simpl in Hinp.
  destruct (eq_dec i1 (PI_id pinfo)); subst.
    rewrite lookupAL_updateAddAL_eq in Hlkp.
    inv Hlkp.
    destruct Hwfgvs2 as [J1 J2]; auto.
    split; auto.
      intros. unfold wf_non_alloca_GVs.
      apply Hinc2 in Hin0. simpl in Hin0.
      destruct (id_dec id0 (PI_id pinfo)); subst; auto.
      rewrite <- lookupAL_updateAddAL_neq in Hlk0; auto.
      apply J1 in Hlk0; auto.

    clear Hwfgvs2.
    rewrite <- lookupAL_updateAddAL_neq in Hlkp; auto.
    destruct Hinp as [EQ | Hinp]; subst; try congruence.
    assert (Hlkp':=Hlkp).
    apply HwfDef in Hlkp; auto.
    destruct Hlkp as [J1 J2].
    split; auto.
      intros.
      destruct (id_dec i1 id0); subst.
        rewrite lookupAL_updateAddAL_eq in Hlk0.
        inv Hlk0. apply Hwfgvs1 in Hlkp'; auto.
        unfold wf_non_alloca_GVs.
        destruct (id_dec id0 (PI_id pinfo)); subst; auto.

        rewrite <- lookupAL_updateAddAL_neq in Hlk0; auto.
        apply Hinc2 in Hin0.
        simpl in Hin0.
        destruct Hin0 as [Hin0 | Hin0]; subst; try congruence; auto.
Qed.

Lemma preservation_helper1: forall los nts Ps S F l1 ps1 cs1' c0 tmn ifs
  (HwfS : wf_system ifs S)
  (HMinS : moduleInSystemB (module_intro los nts Ps) S = true)
  (HFinPs : InProductsB (product_fdef F) Ps = true)
  (HBinF : blockInFdefB (block_intro l1 ps1 (cs1' ++ [c0]) tmn) F = true),
  ~ In (getCmdLoc c0) (getCmdsLocs cs1').
Proof.
  intros.
  eapply wf_system__uniq_block with (f:=F) in HwfS; eauto.
  simpl in HwfS.
  apply NoDup_inv in HwfS.
  destruct HwfS as [_ J].
  apply NoDup_inv in J.
  destruct J as [J _].
  rewrite getCmdsLocs_app in J.
  simpl in J.
  apply NoDup_last_inv in J. auto.
Qed.

Lemma preservation_helper2: forall los nts Ps S F l1 ps1 cs1' c0 tmn ifs c cs
  (HwfS : wf_system ifs S)
  (HMinS : moduleInSystemB (module_intro los nts Ps) S = true)
  (HFinPs : InProductsB (product_fdef F) Ps = true)
  (HBinF : blockInFdefB 
            (block_intro l1 ps1 (cs1' ++ [c0] ++ [c] ++ cs) tmn) F = true),
  NoDup (getCmdsLocs (cs1' ++ [c0] ++ [c] ++ cs)).
Proof.
  intros.
  eapply wf_system__uniq_block with (f:=F) in HwfS; eauto.
  simpl in HwfS.
  apply NoDup_inv in HwfS.
  destruct HwfS as [_ J].
  apply NoDup_inv in J.
  destruct J as [J _]. auto.
Qed.

Definition inscope_of_pc f b cs tmn : option (list id) :=
  match cs with
  | nil => inscope_of_tmn f b tmn
  | c::_ => inscope_of_cmd f b c
  end.

Lemma impure_cmd_non_updated_preserves_wf_EC : forall maxb pinfo TD M M' lc F B 
  als tmn cs c0 l1 ps1 cs1' ifs S
  (Heq: B = block_intro l1 ps1 (cs1' ++ c0 :: cs) tmn)
  (HwfS: wf_system ifs S) los nts (Heq': TD = (los, nts)) Ps
  (HMinS: moduleInSystemB (module_intro los nts Ps) S = true)
  (HFinPs: InProductsB (product_fdef F) Ps = true)
  (HBinF: blockInFdefB B F = true)
  (Hid : getCmdID c0 = None)
  (Hwfdefs: forall ids0,
              F = (PI_f pinfo) ->
              inscope_of_pc F B (c0::cs) tmn = Some ids0 ->
              wf_defs maxb pinfo TD M lc ids0 als ->
              wf_defs maxb pinfo TD M' lc ids0 als)
  (Hwflc: wf_lc M lc -> wf_lc M' lc)
  (HwfEC: wf_ExecutionContext maxb pinfo TD M 
            {| Opsem.CurFunction := F;
               Opsem.CurBB := B;
               Opsem.CurCmds := c0 :: cs;
               Opsem.Terminator := tmn;
               Opsem.Locals := lc;
               Opsem.Allocas := als |}),
  wf_ExecutionContext maxb pinfo TD M'
    {| Opsem.CurFunction := F;
       Opsem.CurBB := B;
       Opsem.CurCmds := cs;
       Opsem.Terminator := tmn;
       Opsem.Locals := lc;
       Opsem.Allocas := als |}.
Proof.
  simpl. intros.
  destruct HwfEC as [J1 J2].
  split; auto.
  destruct (fdef_dec (PI_f pinfo) F); subst; auto.
  remember (inscope_of_cmd (PI_f pinfo) 
    (block_intro l1 ps1 (cs1' ++ c0 :: cs) tmn) c0) as R1. 
  assert (HeqR1':=HeqR1).
  unfold inscope_of_cmd, inscope_of_id in HeqR1'.

  destruct R1; try solve [inversion J1].
  repeat (split; try solve [auto]).
      destruct cs; simpl_env in *.
      SSSSCase "cs = nil".
        assert (~ In (getCmdLoc c0) (getCmdsLocs cs1')) 
          as Hnotin.
          eapply preservation_helper1; eauto.

        apply inscope_of_cmd_tmn in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1' J2']].
        rewrite <- J1'.
        assert (In c0 (cs1' ++ [c0])) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc; 
          eauto.
        assert (HwfF:=HFinPs). eapply wf_system__wf_fdef in HwfF; eauto.
        rewrite Hid in J2'. 
        eapply wf_defs_eq; eauto.       

      SSSSCase "cs <> nil".
        assert (NoDup (getCmdsLocs (cs1' ++ [c0] ++ [c] ++ cs))) 
          as Hnodup.
          eapply preservation_helper2; eauto.

        apply inscope_of_cmd_cmd in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1' J2']].        
        rewrite <- J1'.
        assert (In c0 (cs1' ++ [c0] ++ [c] ++ cs)) 
          as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc; 
          eauto.
        rewrite Hid in J2'. 
        eapply wf_defs_eq; eauto.
Qed.

(* We need a generic proof for this one and the one for atom *)
Lemma NoDup_disjoint : forall (l1 l2 : list Z) (i0 : Z),
  NoDup (l1 ++ l2) -> In i0 l2 -> ~ In i0 l1.
Admitted.

Lemma wf_globals_disjoint_with_runtime_alloca: forall maxb gl g td c0 mb t
  (Hwfg: wf_globals maxb gl)
  (Hc2g : ret g = @Opsem.const2GV DGVs td gl c0)
  (Hle: maxb < mb),
  no_alias g ($ blk2GV td mb # typ_pointer t $).
Admitted.

Lemma undef_disjoint_with_runtime_alloca: forall g td mb t1 t2
  (Hc2g : ret g = gundef td t1),
  no_alias g ($ blk2GV td mb # typ_pointer t2 $).
Admitted.

Lemma preservation_return_helper: forall (g : GVsT DGVs) pinfo lc' Mem'
  als' td maxb Mem ECs lc gl t Result
  (HeqR1 : ret g = Opsem.getOperandValue td Result lc gl)
  (g0 : GVsT DGVs)
  (HeqR2 : ret g0 = lift_op1 DGVs (fit_gv td t) g t)
  (Hwfg : wf_globals maxb gl)
  (l0 : list atom)
  (Hfr1 : wf_ECStack_head_tail maxb pinfo td Mem lc
           ((PI_f pinfo, lc')
            :: List.map
                 (fun ec : Opsem.ExecutionContext =>
                  let '{| Opsem.CurFunction := f; Opsem.Locals := lc |} :=
                       ec in (f, lc)) ECs))
  (Hinscope2 : wf_defs maxb pinfo td Mem' lc' l0 als')
  (gvsa : GVsT DGVs)
  (Hpindom : In (PI_id pinfo) l0)
  (Hlkp : lookupAL (GVsT DGVs) lc' (PI_id pinfo) = ret gvsa),
  no_alias g0 gvsa.
Proof.
  intros.
  assert (Hlkp':=Hlkp).
  apply Hinscope2 in Hlkp'; auto.
  destruct Hlkp' as [[[mb [EQ [Hin Hbound]]] _] _]; subst.
  edestruct Hfr1 with (ec0:=(PI_f pinfo, lc')) as [_ [G _]]; simpl; eauto.
  clear Hfr1.
  simpl in G.
  Local Transparent lift_op1. simpl in HeqR2.
  unfold MDGVs.lift_op1, fit_gv in HeqR2.
  destruct (getTypeSizeInBits td t); tinv HeqR2.
  destruct (sizeGenericValue g =n= nat_of_Z (ZRdiv (Z_of_nat n) 8)).
    inv HeqR2.
    destruct Result; simpl in HeqR1; eauto.            
    eapply wf_globals_disjoint_with_runtime_alloca; eauto.
  
    eapply undef_disjoint_with_runtime_alloca; eauto.
Qed.

Lemma wf_als_split: forall maxb M als als',
  wf_als maxb M (als++als') -> wf_als maxb M als /\ wf_als maxb M als'.
Proof.
  intros.
  destruct H as [J1 J2].
  apply NoDup_split in J1.
  destruct J1 as [J11 J12].
  split.
    split; auto.
      intros. apply J2. apply in_or_app; auto.
    split; auto.
      intros. apply J2. apply in_or_app; auto.
Qed.

Ltac SSSSSCase name := Case_aux subsubsubsubsubcase name.
Ltac SSSSSSCase name := Case_aux subsubsubsubsubsubcase name.

Lemma free_allocas_preserves_mload_inv: forall TD Mem' gptr ty al gvsa Mem als
  (H1 : mload TD Mem' gptr ty al = ret gvsa)
  (H2 : free_allocas TD Mem als = ret Mem'),
  mload TD Mem gptr ty al = ret gvsa.
Proof.
Admitted.

Lemma free_allocas_preserves_mload: forall TD Mem als Mem' t al gv mb
  (H0 : ~ In mb als)
  (H1 : free_allocas TD Mem als = ret Mem')
  (H2 : mload TD Mem ($ blk2GV TD mb # typ_pointer t $) t al = ret gv),
  mload TD Mem' ($ blk2GV TD mb # typ_pointer t $) t al = ret gv.
Admitted.

Lemma free_allocas_preserves_wf_alloca: forall maxb pinfo TD Mem gvsa als0 als Mem',
  wf_alloca_GVs maxb pinfo TD Mem gvsa als0 ->
  NoDup (als ++ als0) ->
  free_allocas TD Mem als = ret Mem' ->
  wf_alloca_GVs maxb pinfo TD Mem' gvsa als0.
Proof.
  intros.
  unfold wf_alloca_GVs in *.
  destruct H as [J1 [J2 J3]].
  split; auto.
  split.
    intros gptr gvs1 ty al J.  
    eapply free_allocas_preserves_mload_inv in J; eauto.

    destruct J3 as [gv J3].
    exists gv.
    destruct J1 as [mb [J11 [J12 J13]]]; subst.
    eapply free_allocas_preserves_mload; eauto.
    eapply NoDup_disjoint in H0; eauto.
Qed.

Lemma free_allocas_preserves_wf_defs: forall maxb pinfo TD Mem lc' l0 als0 als Mem',
  wf_defs maxb pinfo TD Mem lc' l0 als0 ->
  NoDup (als ++ als0) ->
  free_allocas TD Mem als = ret Mem' ->
  wf_defs maxb pinfo TD Mem' lc' l0 als0.
  (* This is only true if als is always disjoint with pinfo.id *) 
Proof.
  intros. unfold wf_defs in *. intros.
  apply H in Hlkp; auto. clear H.
  destruct Hlkp as [J1 J2]. 
  split; eauto using free_allocas_preserves_wf_alloca.
Qed.

Lemma free_allocas_preserves_wf_lc: forall td Mem als Mem' lc,
  wf_lc Mem lc -> free_allocas td Mem als = ret Mem' -> wf_lc Mem' lc.
Admitted.

Lemma returnUpdateLocals__wf_lc: forall maxb td Result (lc:DGVMap) gl c' 
  lc' Mem lc''
  (H1 : Opsem.returnUpdateLocals td c' Result lc lc' gl = ret lc'')
  (Hwflc1 : wf_lc Mem lc) (Hwflc2 : wf_lc Mem lc')
  (Hwfg : wf_globals maxb gl) (Hgbound : maxb < Mem.nextblock Mem),
  wf_lc Mem lc''.
Admitted.

Lemma free_allocas_preserves_wf_ECStack: forall maxb pinfo td Mem als Mem' ECs,
  wf_ECStack maxb pinfo td Mem ECs ->
  free_allocas td Mem als = ret Mem' ->
  NoDup (als ++ (flat_map
                  (fun ec : Opsem.ExecutionContext =>
                   let '{| Opsem.Allocas := als |} := ec in als)
                   ECs)) ->
  wf_ECStack maxb pinfo td Mem' ECs.
Admitted.

Lemma free_allocas_preserves_wf_ECStack_head_tail : forall maxb pinfo td M M' 
  lc als lc' F' lc'' ECs gl Result c',
  free_allocas td M als = ret M' ->
  Opsem.returnUpdateLocals td c' Result lc lc' gl = ret lc'' ->
  wf_ECStack_head_tail maxb pinfo td M lc ((F', lc')::ECs) ->
  wf_ECStack_head_tail maxb pinfo td M lc' ECs ->
  wf_ECStack_head_tail maxb pinfo td M' lc'' ECs.
Admitted.

Lemma free_allocas_preserves_wf_Mem: forall maxb td Mem als Mem',
  wf_Mem maxb td Mem -> free_allocas td Mem als = ret Mem' -> 
  wf_Mem maxb td Mem'.
Admitted.

Lemma free_allocas_preserves_wf_als : forall maxb TD M M' als als0
  (Hfree: free_allocas TD M als0 = ret M') 
  (Hwf: wf_als maxb M als),
  wf_als maxb M' als.
Admitted.

Lemma preservation_return : forall maxb pinfo (HwfPI : WF_PhiInfo pinfo)  
  F B rid RetTy Result lc F' B' c' cs' tmn' lc' EC Mem als als' cfg
  EC1 EC2 (Hwfg: wf_globals maxb (OpsemAux.Globals cfg))
  (EQ1:EC1 = {| Opsem.CurFunction := F;
                Opsem.CurBB := B;
                Opsem.CurCmds := nil;
                Opsem.Terminator := insn_return rid RetTy Result;
                Opsem.Locals := lc;
                Opsem.Allocas := als |})
  (EQ2:EC2 = {| Opsem.CurFunction := F';
                Opsem.CurBB := B';
                Opsem.CurCmds := c' :: cs';
                Opsem.Terminator := tmn';
                Opsem.Locals := lc';
                Opsem.Allocas := als' |})
  (Hinv : OpsemPP.wf_State cfg
           {| Opsem.ECS := EC1 :: EC2 :: EC;
              Opsem.Mem := Mem |})
  Mem' lc'' (H : Instruction.isCallInst c' = true)
  (H0 : free_allocas (OpsemAux.CurTargetData cfg) Mem als = ret Mem')
  (H1 : Opsem.returnUpdateLocals 
          (OpsemAux.CurTargetData cfg) c' 
            Result lc lc' (OpsemAux.Globals cfg) = ret lc'')
  (HwfS1 : wf_State maxb pinfo cfg
            {| Opsem.ECS := EC1 :: EC2 :: EC;
               Opsem.Mem := Mem |}),
  wf_State maxb pinfo cfg
     {| Opsem.ECS :=
             {| Opsem.CurFunction := F';
                Opsem.CurBB := B';
                Opsem.CurCmds := cs';
                Opsem.Terminator := tmn';
                Opsem.Locals := lc'';
                Opsem.Allocas := als' |} :: EC;
        Opsem.Mem := Mem' |}.
Proof.
Local Opaque inscope_of_tmn inscope_of_cmd.

  intros. subst. destruct cfg as [S [los nts] Ps gl fs].
  destruct Hinv as 
    [_ [HwfSystem [HmInS [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [_ [_ [l1 [ps1 [cs1' Heq1]]]]]]]] 
     [
       [
         [Hreach2 [HBinF2 [HFinPs2 [_ [_ [l2 [ps2 [cs2' Heq2]]]]]]]]
         [HwfEC0 HwfCall]
       ]
       HwfCall'
     ]
    ]]]]]; subst.
  fold (@OpsemPP.wf_ECStack DGVs) in HwfEC0.
  destruct HwfS1 as 
    [
      [[Hinscope1 Hwflc1] [[[Hinscope2 Hwflc2] [HwfECs Hfr2]] Hfr1]] 
      [Hdisjals HwfM]
    ]. simpl. simpl in Hdisjals.
  fold wf_ECStack in HwfECs.
  assert (Hdisjals':=Hdisjals).
  destruct Hdisjals' as [Hdisjals' _].
  split.
  SCase "wf_ECStack".
    split.
    SSCase "wf_EC".
    split.
    SSSCase "sdom".

    destruct (fdef_dec (PI_f pinfo) F'); subst; auto.
    remember (inscope_of_cmd 
      (PI_f pinfo) (block_intro l2 ps2 (cs2' ++ c' :: cs') tmn') c') as R2.
    destruct R2; try solve [inversion Hinscope2].

    remember (getCmdID c') as R.
    destruct c'; try solve [inversion H].
    assert (In (insn_call i0 n c t v p) 
      (cs2'++[insn_call i0 n c t v p] ++ cs')) as HinCs.
      apply in_or_app. right. simpl. auto.
    assert (Hwfc := HBinF2).
    eapply wf_system__wf_cmd with (c:=insn_call i0 n c t v p) in Hwfc; eauto.
    assert (wf_fdef nil S (module_intro los nts Ps) (PI_f pinfo)) as HwfF.
      eapply wf_system__wf_fdef; eauto.
    assert (uniqFdef (PI_f pinfo)) as HuniqF.
      eapply wf_system__uniqFdef; eauto.

    assert (NoDup (als ++ als')) as Hnodup.
      rewrite_env 
        ((als ++ als') ++ 
          flat_map
            (fun ec : Opsem.ExecutionContext =>
             let '{| Opsem.Allocas := als |} := ec in als) EC) in Hdisjals'.
      apply NoDup_split in Hdisjals'.
      destruct Hdisjals'; auto.
    eapply free_allocas_preserves_wf_defs in Hinscope2; eauto. clear Hnodup.
    destruct cs'.
    SSSSCase "cs' = nil".
      assert (~ In (getCmdLoc (insn_call i0 n c t v p)) (getCmdsLocs cs2')) 
        as Hnotin.
        eapply preservation_helper1; eauto.

      assert (HeqR2':=HeqR2).
      apply inscope_of_cmd_tmn in HeqR2; auto.
      destruct HeqR2 as [ids2 [J1 J2]].
      simpl_env. rewrite <- J1.
      unfold Opsem.returnUpdateLocals in H1. simpl in H1.
      remember (Opsem.getOperandValue (los,nts) Result lc gl) as R1.
      destruct R1; try solve [inv H1].
      destruct R.
      SSSSSCase "c' defines a variable".
        destruct n; inv HeqR.
        destruct t; tinv H1.

        remember (MDGVs.lift_op1 (fit_gv (los, nts) t) g t) as R2.
        destruct R2; inv H1.

        apply wf_defs_updateAddAL with (ids1:=l0); auto.
          split.
            eapply preservation_return_helper; eauto.

            intro; subst.
            admit. (* PI_id pinfo cannot be of an id for callsite *) 

      SSSSSCase "c' defines nothing".
        destruct n; inv HeqR. inv H1.
        simpl in J2.
        eapply wf_defs_eq; eauto. 
        
    SSSSCase "cs' <> nil".
      assert (NoDup (getCmdsLocs (cs2' ++ [insn_call i0 n c t v p] ++ [c0] ++ 
        cs'))) as Hnodup.
        eapply preservation_helper2; eauto.

      assert (HeqR2':=HeqR2). simpl_env in HeqR2.
      apply inscope_of_cmd_cmd in HeqR2; auto.
      destruct HeqR2 as [ids2 [J1 J2]].        
      simpl_env. rewrite <- J1.
      unfold Opsem.returnUpdateLocals in H1. simpl in H1.
      remember (Opsem.getOperandValue (los,nts) Result lc gl) as R1.
      destruct R1; try solve [inv H1].
      destruct R.
      SSSSSCase "c' defines a variable".
        destruct n; inv HeqR.
        destruct t; tinv H1.
        remember (MDGVs.lift_op1 (fit_gv (los, nts) t) g t) as R2.
        destruct R2; inv H1.
        inv Hwfc. inv H16. inv H7. inv H18.

        apply wf_defs_updateAddAL with (ids1:=l0); auto.
          split.
            eapply preservation_return_helper; eauto.

            intro; subst.
            admit. (* PI_id pinfo cannot be of an id for callsite *) 

      SSSSSCase "c' defines nothing".
        destruct n; inv HeqR. inv H1.
        simpl in J2.
        eapply wf_defs_eq; eauto. 

      SSSCase "wflc".
        clear - Hwflc1 Hwflc2 H1 Hwfg HwfM H0.
        eapply free_allocas_preserves_wf_lc in H0; eauto.
        destruct HwfM.
        eapply returnUpdateLocals__wf_lc in H1; eauto.

    split.
    SSCase "wf_ECs".
      eapply free_allocas_preserves_wf_ECStack; eauto.
      apply NoDup_strenthening in Hdisjals'; auto.

    SSCase "wf_ECs_head_tail".
      simpl in Hfr1, Hfr2.
      eapply free_allocas_preserves_wf_ECStack_head_tail; eauto.

  split.
  SCase "Disjoint Allocas".
    apply wf_als_split in Hdisjals.
    destruct Hdisjals; auto.
    eapply free_allocas_preserves_wf_als; eauto.

  SCase "wfM".
    eapply free_allocas_preserves_wf_Mem; eauto.

Transparent inscope_of_tmn inscope_of_cmd.
Qed.

Ltac unfold_blk2GV := unfold blk2GV, ptr2GV, val2GV.

Lemma gptr_spec: forall pinfo gv3 mb td
  (Hwfgv : ~
          (exists blk : Values.block,
             exists ofs : int32, gv3 = mk_gptr blk ofs)),
  gv3 <> $ blk2GV td mb # typ_pointer (PI_typ pinfo) $.
Proof.
  intros. destruct td.
  intro J. subst. apply Hwfgv.
  unfold_blk2GV. unfold mk_gptr.
Local Transparent gv2gvs.
  unfold gv2gvs. simpl. unfold MDGVs.gv2gvs. eauto.
Opaque gv2gvs. 
Qed.

Lemma updateAddAL__wf_lc: forall gv3 Mem0 lc id0
  (Hwfgv: forall blk ofs, gv3 = mk_gptr blk ofs -> blk < Mem.nextblock Mem0)
  (Hwflc: wf_lc Mem0 lc),
  wf_lc Mem0 (updateAddAL (GVsT DGVs) lc id0 gv3).
Proof.
  intros. unfold wf_lc in *. intros.
  destruct (id_dec id0 id1); subst.
    rewrite lookupAL_updateAddAL_eq in H. inv H. eauto.

    rewrite <- lookupAL_updateAddAL_neq in H; auto.
    eapply Hwflc; eauto.
Qed.

Lemma updateAddAL__wf_ECStack_head_tail: forall maxb pinfo td M lc ECs
  id0 gv3 
  (Hwfgv: forall blk ofs, gv3 = mk_gptr blk ofs -> blk < Mem.nextblock M),
  wf_ECStack_head_tail maxb pinfo td M lc ECs ->
  wf_ECStack_head_tail maxb pinfo td M (updateAddAL (GVsT DGVs) lc id0 gv3) ECs.
Proof.
  unfold wf_ECStack_head_tail, wf_ECStack_head_in_tail in *.
  intros.
  apply H in H2; auto.
  destruct H2 as [J1 [J2 J3]].
  split; auto.
  split; auto.
    intros. 
    destruct (id_dec id0 id1); subst.
      rewrite lookupAL_updateAddAL_eq in H2.
      inv H2. 
      admit.

      rewrite <- lookupAL_updateAddAL_neq in H2; eauto.
Qed.

Definition wf_GVs_in_EC (maxb:Values.block) (pinfo:PhiInfo) TD M 
  (ec:Opsem.ExecutionContext)(id1:id)(gv1:GVsT DGVs) : Prop :=
let '(Opsem.mkEC f b cs tmn lc als) := ec in
(if (fdef_dec (PI_f pinfo) f) then 
  forall ids0, 
    inscope_of_pc f b cs tmn = Some ids0 ->
    wf_defs maxb pinfo TD M lc ids0 als ->
    wf_GVs maxb pinfo TD M lc ids0 als id1 gv1
else True) /\
(forall blk ofs, gv1 = mk_gptr blk ofs -> blk < Mem.nextblock M).

Lemma preservation_pure_cmd_updated_case : forall (F : fdef)(B : block)
  (lc : DGVMap)(gv3 : GVsT DGVs) (cs : list cmd) (tmn : terminator) id0 c0 Mem0 
  als ECs pinfo 
  (HwfPI : WF_PhiInfo pinfo) (Hid : Some id0 = getCmdID c0) cfg maxb
  EC
  (Heq: EC = {| Opsem.CurFunction := F;
                Opsem.CurBB := B;
                Opsem.CurCmds := c0 :: cs;
                Opsem.Terminator := tmn;
                Opsem.Locals := lc;
                Opsem.Allocas := als |})
  (Hwfgv : wf_GVs_in_EC maxb pinfo (OpsemAux.CurTargetData cfg) Mem0 EC id0 gv3)
  (Hinv : OpsemPP.wf_State cfg
           {| Opsem.ECS := EC :: ECs;
              Opsem.Mem := Mem0 |})
  (HwfS1 : wf_State maxb pinfo cfg
            {| Opsem.ECS := EC :: ECs;
               Opsem.Mem := Mem0 |}),
   wf_State maxb pinfo cfg
     {|
     Opsem.ECS := {|
            Opsem.CurFunction := F;
            Opsem.CurBB := B;
            Opsem.CurCmds := cs;
            Opsem.Terminator := tmn;
            Opsem.Locals := updateAddAL (GVsT DGVs) lc id0 gv3;
            Opsem.Allocas := als |} :: ECs;
     Opsem.Mem := Mem0 |}.
Proof.
Local Opaque inscope_of_cmd inscope_of_tmn.

  intros. subst. destruct Hwfgv as [Hwfgv1 Hwfgv2].
  destruct cfg as [S [los nts] Ps gl fs].
  destruct Hinv as 
    [_ [HwfSystem [HmInS [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [_ [_ [l1 [ps1 [cs1' Heq1]]]]]]]] 
     [HwfEC0 HwfCall]
    ]]]]]; subst.
  fold (@OpsemPP.wf_ECStack DGVs) in HwfEC0.
  destruct HwfS1 as 
    [[[Hinscope1 Hwflc1] [HwfECs Hfr2]] [Hdisjals HwfM]].
  simpl. simpl in Hdisjals.
  fold wf_ECStack in HwfECs.
  simpl in Hwfgv1.
  split; auto.
  SCase "wf_ECStack".
    split.
    SSCase "wf_EC".
    split.
    SSSCase "sdom".
    destruct (fdef_dec (PI_f pinfo) F); subst; auto.

  remember (inscope_of_cmd (PI_f pinfo) 
    (block_intro l1 ps1 (cs1' ++ c0 :: cs) tmn) c0) as R1. 
  assert (HeqR1':=HeqR1).

Transparent inscope_of_cmd.

  unfold inscope_of_cmd, inscope_of_id in HeqR1'.
  destruct R1; try solve [inversion Hinscope1].
  repeat (split; try solve [auto]).
      assert (Hid':=Hid).
      symmetry in Hid.
      apply getCmdLoc_getCmdID in Hid.
      subst.
      destruct cs; simpl_env in *.
      SSSSCase "cs = nil".
        assert (~ In (getCmdLoc c0) (getCmdsLocs cs1')) as Hnotin.
          (* this lemma should be lifted to the top *)
          eapply preservation_helper1; eauto.

        apply inscope_of_cmd_tmn in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].        
        rewrite <- J1.
        assert (In c0 (cs1' ++ [c0])) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc; 
          eauto.
        rewrite <- Hid' in J2.
        assert (HwfF:=HFinPs1). eapply wf_system__wf_fdef in HwfF; eauto.
        eapply wf_defs_updateAddAL; eauto.

      SSSSCase "cs <> nil".
        assert (NoDup (getCmdsLocs (cs1' ++ [c0] ++ [c] ++ cs))) as Hnodup.
          (* this lemma should be lifted to the top *)
          eapply preservation_helper2; eauto.

        apply inscope_of_cmd_cmd in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].        
        rewrite <- J1.
        assert (In c0 (cs1' ++ [c0] ++ [c] ++ cs)) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc; 
          eauto.
        rewrite <- Hid' in J2.
        assert (HwfF:=HFinPs1). eapply wf_system__wf_fdef in HwfF; eauto.
        eapply wf_defs_updateAddAL; eauto.

      SSSCase "wflc".
        apply updateAddAL__wf_lc; auto.

    split; auto.
    SSCase "wf_ECs_head_tail".
      simpl in Hfr2.
      eapply updateAddAL__wf_ECStack_head_tail; eauto.

Transparent inscope_of_cmd inscope_of_tmn.

Qed.

Lemma BOP__wf_GVs_in_EC : forall (v : value) (v0 : value) (id1 : id) (bop0 : bop)
  gvs3 TD bop0 sz0 lc gl EC Mem0 td pinfo maxb (Hneq: id1 <> PI_id pinfo)
  (H11 : BOP TD lc gl bop0 sz0 v v0 = ret gvs3),
  wf_GVs_in_EC maxb pinfo td Mem0 EC id1 gvs3.
Proof.
  intros. 
  unfold wf_GVs_in_EC. destruct EC.
  split.
    destruct (fdef_dec (PI_f pinfo) CurFunction); subst; auto.
    intros.
    split; intros; subst; try congruence.
      admit. (* BOP isnt ptr *)

    intros. subst.
    admit. (* BOP isnt ptr *)
Qed.

Definition wf_use_at_head (pinfo:PhiInfo) (ids0:list id) (v:value) :=
used_in_value (PI_id pinfo) v = false /\
match v with
| value_const _ => True
| value_id vid => In vid ids0
end.

Lemma operand__no_alias_with__head: forall maxb pinfo TD lc mptr0 mptrs gl v als
  (Hgetop : Opsem.getOperandValue TD v lc gl = ret mptrs)
  (Hin : mptr0 @ mptrs) (Hwfgl : wf_globals maxb gl) ids0 M
  (Hwfu: wf_use_at_head pinfo ids0 v) (Hwf: wf_defs maxb pinfo TD M lc ids0 als)
  (gvsa : GVsT DGVs) (Hpindom : In (PI_id pinfo) ids0)
  (Hlkp : lookupAL (GVsT DGVs) lc (PI_id pinfo) = ret gvsa),
  no_alias mptr0 gvsa.
Proof.
  intros.
  apply Hwf in Hlkp; auto.
  destruct Hlkp as [[J1 [J4 [gv J3]]] J2].
  inv Hin.
  destruct v; simpl in Hgetop.
    destruct Hwfu as [Hwfu1 Hwfu2].        
    apply J2 in Hgetop; auto.
    unfold wf_non_alloca_GVs in Hgetop.
    destruct (id_dec i0 (PI_id pinfo)); subst; auto.
      inv Hwfu1. 
      destruct (id_dec (PI_id pinfo) (PI_id pinfo)); try congruence.
        inv H0.
  
    destruct J1 as [mb [J11 [J12 J13]]]; subst.
    eapply wf_globals_disjoint_with_runtime_alloca; eauto.
Qed.

Lemma wf_globals__le_maxb: forall maxb gl td c0 
  (Hwfg: wf_globals maxb gl) blk ofs
  (Hc2g : ret mk_gptr blk ofs = @Opsem.const2GV DGVs td gl c0),
  blk <= maxb.
Admitted.

Lemma operand__lt_nextblock: forall maxb TD M (lc:DGVMap) blk ofs gl
  (Hwfgl : wf_globals maxb gl) v mptrs (Hlt: maxb < Mem.nextblock M)
  (Hwflc: wf_lc M lc) 
  (Hin: mk_gptr blk ofs @ mptrs) 
  (Hgetop : Opsem.getOperandValue TD v lc gl = ret mptrs),
  blk < Mem.nextblock M.
Proof.
  intros.
  inv Hin.
  destruct v; simpl in Hgetop.
    apply Hwflc in Hgetop; auto.

    eapply wf_globals__le_maxb in Hwfgl; eauto.
    omega.
Qed.     

Lemma CAST__wf_GVs_in_EC : forall (v : value) (id1 : id)
  gvs2 TD gl EC Mem pinfo maxb castop0 t1 t2 
  (Hwflc: wf_lc Mem (@Opsem.Locals DGVs EC)) 
  (Hwfgl: wf_globals maxb gl) (HwfM: maxb < Mem.nextblock Mem)
  (Hwfv: forall ids0,
         let '(Opsem.mkEC F B cs tmn _ _) := EC in
         F = (PI_f pinfo) ->
         inscope_of_pc F B cs tmn = Some ids0 ->
         wf_use_at_head pinfo ids0 v)
  (Hneq: id1 <> PI_id pinfo)
  (H11 : Opsem.CAST TD (@Opsem.Locals DGVs EC) gl castop0 t1 v t2 
           = ret gvs2),
  wf_GVs_in_EC maxb pinfo TD Mem EC id1 gvs2.
Proof.
  intros. 
  unfold wf_GVs_in_EC. destruct EC.
  apply OpsemProps.CAST_inversion in H11.
  destruct H11 as [gv1 [J1 J2]].
  split.
    destruct (fdef_dec (PI_f pinfo) CurFunction); subst; auto.
    intros.
    split; intros; subst; try congruence.
      assert (H2':=H2).
      apply H0 in H2; auto.
      destruct H2 as [[J5 [J6 J3]] J4]; eauto.
      eapply operand__no_alias_with__head with (als:=Allocas) (mptr0:=gv1)
        (M:=Mem) in J1; eauto.
        clear - J1 J2. admit. (* CAST is aliasing *)

    intros. subst.
    assert (exists ofs', gv1 = mk_gptr blk ofs') as EQ. admit. (* CAST inv *)
    destruct EQ as [ofs' EQ]; subst.
    eapply operand__lt_nextblock in J1; eauto.
Qed.

Lemma wf_EC__wf_lc : forall maxb pinfo TD M EC,
  wf_ExecutionContext maxb pinfo TD M EC ->
  wf_lc M (Opsem.Locals EC).
Admitted.

Lemma mload__wf_GVs_in_EC : forall (v : value) (v0 : value) (id1 : id) 
  gvs3 t align0 EC Mem td pinfo maxb mp
  (Hneq: id1 <> PI_id pinfo) (HwfM: wf_Mem maxb td Mem)
  (H1 : mload td Mem mp t align0 = ret gvs3),
  wf_GVs_in_EC maxb pinfo td Mem EC id1 gvs3.
Proof.
  intros. 
  unfold wf_GVs_in_EC. destruct EC.
  split.
    destruct (fdef_dec (PI_f pinfo) CurFunction); subst; auto.
    intros.
    split; intros; subst; try congruence.
      apply H0 in H3; auto.
      destruct H3 as [[J1 [J2 J3]] _]; eauto.

    intros. subst.
    destruct HwfM as [J1 J2]; eauto.
Qed.

Lemma GEP__wf_GVs_in_EC : forall (v : value) (v0 : value) (id1 : id) 
  mp' TD t gl EC Mem td pinfo maxb (mp:GVsT DGVs) mps 
  inbounds0 vidxs (Hwflc: wf_lc Mem (@Opsem.Locals DGVs EC)) 
  (Hwfgl: wf_globals maxb gl) (HwfM: maxb < Mem.nextblock Mem)
  (Hwfv: forall ids0,
         let '(Opsem.mkEC F B cs tmn _ _) := EC in
         F = (PI_f pinfo) ->
         inscope_of_pc F B cs tmn = Some ids0 ->
         wf_use_at_head pinfo ids0 v)
  (H : Opsem.getOperandValue td v (Opsem.Locals EC) gl = ret mps)
  (H0 : mp @ mps) (Hneq: id1 <> PI_id pinfo)
  (H1 : Opsem.GEP TD t mp vidxs inbounds0 = ret mp'),
  wf_GVs_in_EC maxb pinfo td Mem EC id1 mp'.
Proof.
  intros. 
  unfold wf_GVs_in_EC. destruct EC.
  split.
    destruct (fdef_dec (PI_f pinfo) CurFunction); subst; auto.
    intros.
    split; intros; subst; try congruence.
      assert (H5':=H5).
      apply H3 in H5; auto.
      destruct H5 as [[J1 [J2 J3]] J4]; eauto.
      eapply operand__no_alias_with__head with (als:=Allocas) (mptr0:=mp)
        (M:=Mem) in H; eauto.
        clear - H1 H. admit. (* GEP is aliasing *)

    intros. subst.
    assert (exists ofs', mp = mk_gptr blk ofs') as EQ. admit. (* GEP inv *)
    destruct EQ as [ofs' EQ]; subst.
    eapply operand__lt_nextblock in H; eauto.
Qed.

Lemma initLocals_preserves_wf_ECStack_head_tail: forall Mem (lc:DGVMap) maxb TD 
  F ECs lc' gl (Hwflc1 : wf_lc Mem lc) pinfo gvs la lp
  (Hwfg : wf_globals maxb gl)
  (H3 : Opsem.params2GVs TD lp lc gl = ret gvs)
  (H4 : Opsem.initLocals TD la gvs = ret lc')
  (Hfr2 : wf_ECStack_head_tail maxb pinfo TD Mem lc
            (List.map
               (fun ec : Opsem.ExecutionContext =>
                let '{| Opsem.CurFunction := f; Opsem.Locals := lc |} := ec in
                  (f, lc)) ECs)),
  wf_ECStack_head_tail maxb pinfo TD Mem lc'
    ((F, lc)
      :: List.map
           (fun ec : Opsem.ExecutionContext =>
            let '{| Opsem.CurFunction := f; Opsem.Locals := lc0 |} := ec in
              (f, lc0)) ECs).
Admitted.

Lemma preservation_dbCall_case : forall fid fa rt la va lb gvs los
  nts ifs s lc Ps Mem TD pinfo maxb
  (Huniq: uniqFdef (fdef_intro (fheader_intro fa rt fid la va) lb))
  (HwfF: wf_fdef ifs s (module_intro los nts Ps) 
    (fdef_intro (fheader_intro fa rt fid la va) lb))
  (HwfM : wf_Mem maxb TD Mem)
  (Hinit : Opsem.initLocals TD la gvs = Some lc),
  wf_defs maxb pinfo TD Mem lc (getArgsIDs la) nil.
Proof.
Admitted.

Lemma initLocals_preserves_wf_lc: forall Mem (lc:DGVMap) maxb TD 
  lc' gl (Hwflc1 : wf_lc Mem lc) gvs la lp
  (Hwfg : wf_globals maxb gl)
  (H3 : Opsem.params2GVs TD lp lc gl = ret gvs)
  (H4 : Opsem.initLocals TD la gvs = ret lc')
  (Hfr2 : wf_lc Mem lc),
  wf_lc Mem lc'.
Admitted.

Lemma callExternalProc_preserves_wf_ECStack_head_tail : forall maxb pinfo   
  ECs TD M M' (lc:DGVMap) gvs gvss fid oresult gl lp
  (Hwflc: wf_lc M lc) (Hwfgl: wf_globals maxb gl) (H3 : gvs @@ gvss),
  Opsem.params2GVs TD lp lc gl = ret gvss ->
  OpsemAux.callExternalFunction M fid gvs = ret (oresult, M') ->
  wf_ECStack_head_tail maxb pinfo TD M lc ECs ->
  wf_ECStack_head_tail maxb pinfo TD M' lc ECs.
Admitted.

Lemma callExternalFunction_preserves_wf_ECStack : forall maxb pinfo ECs TD M  
  M' gvs fid oresult, 
  OpsemAux.callExternalFunction M fid gvs = ret (oresult, M') ->
  wf_ECStack maxb pinfo TD M ECs ->
  wf_ECStack maxb pinfo TD M' ECs.
Admitted.

Lemma callExternalProc_preserves_wf_EC : forall maxb pinfo TD M M' rid
  als F B cs tmn gl gvss gvs fid oresult lp (lc:DGVMap) fv ft ca
  (Hwflc: wf_lc M lc) (Hwfgl: wf_globals maxb gl) (H3 : gvs @@ gvss)
  (J1: Opsem.params2GVs TD lp lc gl = ret gvss)
  (J2: OpsemAux.callExternalFunction M fid gvs = ret (oresult, M'))
  (HwfEC: wf_ExecutionContext maxb pinfo TD M 
            {| Opsem.CurFunction := F;
               Opsem.CurBB := B;
               Opsem.CurCmds := insn_call rid true ca ft fv lp :: cs;
               Opsem.Terminator := tmn;
               Opsem.Locals := lc;
               Opsem.Allocas := als |}),
  wf_ExecutionContext maxb pinfo TD M'
   {| Opsem.CurFunction := F;
      Opsem.CurBB := B;
      Opsem.CurCmds := cs;
      Opsem.Terminator := tmn;
      Opsem.Locals := lc;
      Opsem.Allocas := als |}.
Admitted.

Lemma callExternalFunction_preserves_wf_Mem : forall maxb TD M fid gvs M' 
  oresult,
  OpsemAux.callExternalFunction M fid gvs = ret (oresult, M') ->
  wf_Mem maxb TD M ->
  wf_Mem maxb TD M'.
Admitted.

Lemma callExternalFunction_preserves_wf_als : forall M gvs M' maxb als fid 
  oresult
  (Hexcall: OpsemAux.callExternalFunction M fid gvs = ret (oresult, M')) 
  (Hwf: wf_als maxb M als),
  wf_als maxb M' als.
Admitted.

Lemma callExternalFun_preserves_wf_ECStack_head_tail : forall maxb pinfo   
  ECs TD M M' (lc:DGVMap) gvs gvss fid result gl lp g0 rid ft
  (Hwflc: wf_lc M lc) (Hwfgl: wf_globals maxb gl) (H3 : gvs @@ gvss)
  (HeqR : ret g0 = fit_gv TD ft result),
  Opsem.params2GVs TD lp lc gl = ret gvss ->
  OpsemAux.callExternalFunction M fid gvs = ret (Some result, M') ->
  wf_ECStack_head_tail maxb pinfo TD M lc ECs ->
  wf_ECStack_head_tail maxb pinfo TD M' 
    (updateAddAL (GVsT DGVs) lc rid ($ g0 # ft $)) ECs.
Admitted.

Lemma callExternalFun_preserves_wf_EC : forall maxb pinfo TD M M' rid
  als F B cs tmn gl gvss gvs fid result lp (lc:DGVMap) fv ft ca g0
  (Hwflc: wf_lc M lc) (Hwfgl: wf_globals maxb gl) (H3 : gvs @@ gvss)
  (J1: Opsem.params2GVs TD lp lc gl = ret gvss)
  (J2: OpsemAux.callExternalFunction M fid gvs = ret (Some result, M'))
  (HeqR : ret g0 = fit_gv TD ft result)
  (HwfEC: wf_ExecutionContext maxb pinfo TD M 
            {| Opsem.CurFunction := F;
               Opsem.CurBB := B;
               Opsem.CurCmds := insn_call rid false ca ft fv lp :: cs;
               Opsem.Terminator := tmn;
               Opsem.Locals := lc;
               Opsem.Allocas := als |}),
  wf_ExecutionContext maxb pinfo TD M'
   {| Opsem.CurFunction := F;
      Opsem.CurBB := B;
      Opsem.CurCmds := cs;
      Opsem.Terminator := tmn;
      Opsem.Locals := (updateAddAL (GVsT DGVs) lc rid ($ g0 # ft $));
      Opsem.Allocas := als |}.
Admitted.

Lemma free_preserves_mload_inv: forall TD Mem' gptr ty al gvsa Mem mptr0
  (H1 : mload TD Mem' gptr ty al = ret gvsa)
  (H2 : free TD Mem mptr0 = ret Mem'),
  mload TD Mem gptr ty al = ret gvsa.
Proof.
  intros.
  apply mload_inv in H1.
  destruct H1 as [b [ofs [m [mc [J1 [J2 J3]]]]]]; subst.
  unfold mload. simpl. rewrite J2.
  apply free_inv in H2.
  destruct H2 as [blk' [ofs' [hi [lo [J4 [J5 [J6 J7]]]]]]].
  admit. (* Mem Props *)
Qed.

Lemma free_preserves_wf_ECStack_head_tail : forall maxb pinfo TD M M' lc mptr0
  (Hfree: free TD M mptr0 = ret M') ECs 
  (Hwf: wf_ECStack_head_tail maxb pinfo TD M lc ECs),
  wf_ECStack_head_tail maxb pinfo TD M' lc ECs.
Proof.
  unfold wf_ECStack_head_tail, wf_ECStack_head_in_tail.
  intros.
  eapply Hwf in H0; eauto.
  destruct H0 as [[mb [J11 J12]] [J2 J3]]; subst.
  split.
    exists mb. split; auto. admit. (* Mem Prop *)
  split; auto.
    intros.
    eapply free_preserves_mload_inv in H0; eauto.
Qed.

Lemma free_preserves_wf_lc: forall TD Mem' Mem mptr0
  (H2 : free TD Mem mptr0 = ret Mem') lc
  (Hwf: wf_lc Mem lc),
  wf_lc Mem' lc.
Proof.
  unfold wf_lc.
  intros.
  apply Hwf in H.
  apply free_inv in H2.
  destruct H2 as [blk' [ofs' [hi [lo [J4 [J5 [J6 J7]]]]]]].
  admit. (* Mem Props *)
Qed.

Definition wf_use_in_tail (pinfo:PhiInfo) (v:value) :=
used_in_value (PI_id pinfo) v = false.

Lemma free_preserves_mload: forall TD Mem Mem' t al gv gptr gvsa
  (H0 : no_alias gptr gvsa)
  (H1 : free TD Mem gptr = ret Mem')
  (H2 : mload TD Mem gvsa t al = ret gv),
  mload TD Mem' gvsa t al = ret gv.
Proof.
  intros.
  apply free_inv in H1.
  destruct H1 as [blk [ofs [hi [lo [J4 [J5 [J6 J7]]]]]]].
  admit. (* Mem Props *)
Admitted.

Lemma operand__no_alias_with__tail: forall maxb pinfo TD M lc1 lc2 mptr0 gl
  (Hwfgl : wf_globals maxb gl) v mptrs
  (Hht : wf_ECStack_head_in_tail maxb pinfo TD M lc1 (PI_f pinfo, lc2))
  (gvsa : GVsT DGVs) (Hin: mptr0 @ mptrs) 
  (Hlkp : lookupAL (GVsT DGVs) lc2 (PI_id pinfo) = ret gvsa)
  (Hgetop : Opsem.getOperandValue TD v lc1 gl = ret mptrs),
  no_alias mptr0 gvsa.
Proof.
  intros.
  inv Hin.
  apply Hht in Hlkp; auto.
  destruct Hlkp as [[mb [J11 J12]] [Hlkp _]]; subst.
  destruct v; simpl in Hgetop.
    apply Hlkp in Hgetop; auto.
    eapply wf_globals_disjoint_with_runtime_alloca; eauto.
      omega.
Qed.

Lemma free_preserves_wf_defs_in_tail : forall maxb pinfo TD M  
  M' lc1 mptr0 mptrs gl v als lc2 
  (Hgetop: Opsem.getOperandValue TD v lc1 gl = ret mptrs)
  (Hin: mptr0 @ mptrs) (Hwfgl: wf_globals maxb gl)
  (Hfree: free TD M mptr0 = ret M')
  (Hht: wf_ECStack_head_in_tail maxb pinfo TD M lc1 (PI_f pinfo, lc2))
  ids0 (Hwf: wf_defs maxb pinfo TD M lc2 ids0 als),
  wf_defs maxb pinfo TD M' lc2 ids0 als.
Proof.
  intros. unfold wf_defs. 
  intros gvsa Hpindom Hlkp.
  assert (Hlkp':=Hlkp).
  apply Hwf in Hlkp'; auto.
  destruct Hlkp' as [J1 J2].
  split; auto.
    clear J2.
    destruct J1 as [J1 [J4 [gv J3]]].
    split; auto.
      split.
        intros. eapply free_preserves_mload_inv in H; eauto.
        clear J4. 
        assert (no_alias mptr0 gvsa) as J.
          eapply operand__no_alias_with__tail; eauto.
        exists gv. eapply free_preserves_mload; eauto.
Qed.

Lemma free_preserves_wf_defs_at_head : forall maxb pinfo TD M  
  M' lc mptr0 mptrs gl v als
  (Hgetop: Opsem.getOperandValue TD v lc gl = ret mptrs)
  (Hin: mptr0 @ mptrs) (Hwfgl: wf_globals maxb gl)
  (Hfree: free TD M mptr0 = ret M')
  ids0 (Hwfu: wf_use_at_head pinfo ids0 v) 
  (Hwf: wf_defs maxb pinfo TD M lc ids0 als),
  wf_defs maxb pinfo TD M' lc ids0 als.
Proof.
  intros. unfold wf_defs. 
  intros gvsa Hpindom Hlkp.
  assert (no_alias mptr0 gvsa) as J.
    eapply operand__no_alias_with__head; eauto.
  assert (Hlkp':=Hlkp).
  apply Hwf in Hlkp'; auto.
  destruct Hlkp' as [J1 J2].
  split; auto.
    destruct J1 as [J1 [J4 [gv J3]]].
    split; auto.
      split.
        intros. eapply free_preserves_mload_inv in H; eauto.
        exists gv. eapply free_preserves_mload; eauto.
Qed.

Lemma impure_cmd_preserves_wf_EC_tail : forall maxb pinfo TD M  
  M' EC (Hwfpi: WF_PhiInfo pinfo) 
  (Hwfdefs: forall ids0,
     let '(Opsem.mkEC F B cs tmn lc als) := EC in
     F = (PI_f pinfo) ->
     inscope_of_pc F B cs tmn = Some ids0 ->
     wf_defs maxb pinfo TD M lc ids0 als ->
     wf_defs maxb pinfo TD M' lc ids0 als)
  (Hwflc: wf_lc M (@Opsem.Locals DGVs EC) -> wf_lc M' (Opsem.Locals EC))
  (Hwf: wf_ExecutionContext maxb pinfo TD M EC),
  wf_ExecutionContext maxb pinfo TD M' EC.
Proof.
  destruct EC. simpl. intros.
  destruct Hwf as [J1 J2].
  split; auto.
    destruct (fdef_dec (PI_f pinfo) CurFunction); subst; auto.
    destruct CurCmds.    
      remember (inscope_of_tmn (PI_f pinfo) CurBB Terminator) as R.
      destruct R; auto.

      remember (inscope_of_cmd (PI_f pinfo) CurBB c) as R.
      destruct R; auto.
Qed.

Lemma wf_ECStack_head_tail_cons__inv: forall maxb pinfo TD M lc ec1 ecs2,
  wf_ECStack_head_tail maxb pinfo TD M lc (ec1::ecs2) ->
  wf_ECStack_head_in_tail maxb pinfo TD M lc ec1 /\
  wf_ECStack_head_tail maxb pinfo TD M lc ecs2.
Proof.
  intros.
  split.
    apply H; simpl; auto.
    unfold wf_ECStack_head_tail in *. intros. apply H; simpl; auto.
Qed.

Lemma free_preserves_wf_ECStack_in_tail : forall maxb pinfo TD M  
  M' mptr0 mptrs gl v (Hwfpi: WF_PhiInfo pinfo) lc
  (Hgetop: Opsem.getOperandValue TD v lc gl = ret mptrs)
  (Hin: mptr0 @ mptrs) (Hwfgl: wf_globals maxb gl)
  (Hfree: free TD M mptr0 = ret M') ECs
  (Hht: wf_ECStack_head_tail maxb pinfo TD M lc 
          (List.map 
             (fun ec => let '(Opsem.mkEC f _ _ _ lc _) := ec in (f, lc)) ECs))
  (Hwf: wf_ECStack maxb pinfo TD M ECs),
  wf_ECStack maxb pinfo TD M' ECs.
Proof.
  induction ECs; simpl; intros; auto.
    destruct Hwf as [J1 [J2 J3]].
    apply wf_ECStack_head_tail_cons__inv in Hht.
    destruct Hht as [Hht1 Hht2].
    split.
      eapply impure_cmd_preserves_wf_EC_tail with (M:=M); eauto.
        destruct a. intros. subst.
        eapply free_preserves_wf_defs_in_tail; eauto.
        eapply free_preserves_wf_lc; eauto.
    split; auto.
      eapply free_preserves_wf_ECStack_head_tail; eauto.
(* Can this lemma be more generic by making free_preserves_mload_inv generic? *)
Qed.

Lemma free_preserves_wf_Mem : forall maxb TD M M' mptr0
  (Hfree: free TD M mptr0 = ret M') 
  (Hwf: wf_Mem maxb TD M),
  wf_Mem maxb TD M'.
Proof.
  intros. destruct Hwf as [J1 J2].
  split.
    intros. 
    eapply free_preserves_mload_inv in H; eauto.
    apply J1 in H; auto.
    admit. (* Mem Props *)
  
    admit. (* Mem Props *)
Qed.

Lemma free_preserves_wf_als : forall maxb TD M M' mptr0 als
  (Hfree: free TD M mptr0 = ret M') 
  (Hwf: wf_als maxb M als),
  wf_als maxb M' als.
Proof.
  intros. destruct Hwf as [J1 J2].
  split; auto.
    intros. 
    apply J2 in H; auto.
    admit. (* Mem Props *)
Qed.

Lemma mstore_preserves_mload_inv: forall TD Mem' gptr ty al gvs0 Mem gv1 t
  mp2 (H1 : mload TD Mem' gptr ty al = ret gvs0) align
  (H2 : mstore TD Mem mp2 t gv1 align = Some Mem'),
  Some gvs0 = gundef TD ty \/
  gvs0 = gv1 \/
  mload TD Mem gptr ty al = ret gvs0.
Proof.
  intros.
  apply store_inv in H2.
  destruct H2 as [b [ofs [J5 J4]]].
  admit. (* mem prop *)
Admitted.

Lemma mstore_preserves_mload: forall TD Mem' gptr ty al gvs0 Mem gv1 t
  mp2 (H1 : mload TD Mem gptr ty al = ret gvs0) align
  (H2 : mstore TD Mem mp2 t gv1 align = Some Mem')
  (Hna: no_alias mp2 gptr),
  mload TD Mem' gptr ty al = ret gvs0.
Proof.
  admit. (* mem prop *)
Admitted.

Lemma mstore_preserves_mload': forall TD Mem' gptr ty al gvs0 Mem gv1 t
  mp2 (H1 : mload TD Mem gptr ty al = ret gvs0) align
  (H2 : mstore TD Mem mp2 t gv1 align = Some Mem'),
  exists gvs1, mload TD Mem' gptr ty al = ret gvs1.
Proof.
  admit. (* mem prop *)
Admitted.

Lemma mstore_preserves_wf_defs_at_head : forall maxb pinfo TD M  
  M' gl v als lc gvs1 gv1 t mp2 align mps2 vp
  (Hgetop': Opsem.getOperandValue TD vp lc gl = ret mps2)
  (Hgetop: Opsem.getOperandValue TD v lc gl = ret gvs1)
  (Hinp: mp2 @ mps2) (Hin: gv1 @ gvs1) (Hwfgl: wf_globals maxb gl)
  (Hst: mstore TD M mp2 t gv1 align = Some M')
  ids0 (Hwfu: wf_use_at_head pinfo ids0 v) 
  (Hwf: wf_defs maxb pinfo TD M lc ids0 als),
  wf_defs maxb pinfo TD M' lc ids0 als.
Proof.
  intros. unfold wf_defs. 
  intros gvsa Hpindom Hlkp.
  assert (no_alias gv1 gvsa) as J.
    eapply operand__no_alias_with__head with (mptrs:=gvs1); eauto.
  assert (Hlkp':=Hlkp).
  apply Hwf in Hlkp'; auto.
  destruct Hlkp' as [J1 J2].
  split; auto.
    destruct J1 as [[mb [J11 J12]] [J4 [gv J3]]]; subst.
    split; eauto.
    split.
      intros. 
      eapply mstore_preserves_mload_inv in H; eauto.
      destruct H as [H | [H | H]]; subst; eauto.
        eapply undef_disjoint_with_runtime_alloca; eauto.

      eapply mstore_preserves_mload'; eauto.
Qed.

Lemma mstore_preserves_wf_defs_in_tail : forall maxb pinfo TD M  
  M' lc1 gl v als lc2 gvs1 gv1 t mp2 align mps2 vp
  (Hgetop': Opsem.getOperandValue TD vp lc1 gl = ret mps2)
  (Hgetop: Opsem.getOperandValue TD v lc1 gl = ret gvs1)
  (Hinp: mp2 @ mps2) (Hin: gv1 @ gvs1) (Hwfgl: wf_globals maxb gl)
  (Hst: mstore TD M mp2 t gv1 align = Some M')
  (Hht: wf_ECStack_head_in_tail maxb pinfo TD M lc1 (PI_f pinfo, lc2))
  ids0 (Hwf: wf_defs maxb pinfo TD M lc2 ids0 als),
  wf_defs maxb pinfo TD M' lc2 ids0 als.
Proof.
  intros. unfold wf_defs. 
  intros gvsa Hpindom Hlkp.
  assert (Hlkp':=Hlkp).
  apply Hwf in Hlkp'; auto.
  destruct Hlkp' as [J1 J2].
  split; auto.
    clear J2.
    destruct J1 as [[mb [J11 J12]] [J4 [gv J3]]]; subst.
    split; eauto.
    split.
      intros.
      eapply mstore_preserves_mload_inv in Hst; eauto.
      destruct Hst as [G | [G | G]]; subst; eauto.
        eapply undef_disjoint_with_runtime_alloca; eauto.
        eapply operand__no_alias_with__tail; eauto.

      exists gv. 
      eapply mstore_preserves_mload; eauto.
      eapply operand__no_alias_with__tail; eauto.
Qed.

Lemma mstore_preserves_wf_lc: forall TD M' M mp2 t gv1 align
  (Hst: mstore TD M mp2 t gv1 align = Some M') lc
  (Hwf: wf_lc M lc),
  wf_lc M' lc.
Proof.
  unfold wf_lc.
  intros.
  apply Hwf in H.
  apply store_inv in Hst.
  destruct Hst as [blk' [ofs' [J1 J2]]].
  admit. (* Mem Props *)
Qed.

Lemma mstore_preserves_wf_ECStack_head_tail: forall maxb pinfo ECs TD M 
  gv1 align M' lc mp2 t gvs1 gl v1 (Hwfgl: wf_globals maxb gl) EC
  (H0 : Opsem.getOperandValue TD v1 lc gl = Some gvs1)
  (H1 : gv1 @ gvs1)
  (Hst: mstore TD M mp2 t gv1 align = Some M') lc1 (Heq: lc1 = snd EC)
  (Hht: wf_ECStack_head_tail maxb pinfo TD M lc (EC::ECs))
  (Hwf: wf_ECStack_head_tail maxb pinfo TD M lc1 ECs),
  wf_ECStack_head_tail maxb pinfo TD M' lc1 ECs.
Proof.
  intros.
  unfold wf_ECStack_head_tail, wf_ECStack_head_in_tail.
  intros.
  assert (no_alias gv1 gvsa) as J.
    eapply operand__no_alias_with__tail with (M:=M); eauto.
      unfold wf_ECStack_head_in_tail.
      intros. 
      eapply Hht; eauto.
      simpl. right. rewrite <- H2.
      destruct ec0; auto.
  eapply Hwf in H3; eauto.
  destruct H3 as [[mb [J11 J12]] [J2 J3]]; subst.
  split.
    exists mb. split; auto. admit. (* MemProp *)
  split; auto.
    intros.
    eapply mstore_preserves_mload_inv in Hst; eauto.
    destruct Hst as [G | [G | G]]; subst; eauto.
      eapply undef_disjoint_with_runtime_alloca; eauto.
Qed.

Lemma wf_ECStack_head_tail_cons__intro: forall maxb pinfo TD M lc ec1 ecs2,
  wf_ECStack_head_in_tail maxb pinfo TD M lc ec1 ->
  wf_ECStack_head_tail maxb pinfo TD M lc ecs2 ->
  wf_ECStack_head_tail maxb pinfo TD M lc (ec1::ecs2).
Proof.
  intros.
  unfold wf_ECStack_head_tail in *. 
  intros. 
  simpl in H1.
  destruct H1 as [EQ | H1]; subst; auto.
Qed.

Lemma mstore_preserves_wf_ECStack_in_tail : forall maxb pinfo TD M mp2 t align M' gl vp
  (Hwfgl: wf_globals maxb gl) lc gvs1 gv1 v1 (Hwfpi: WF_PhiInfo pinfo) mps2
  (Hgetop': Opsem.getOperandValue TD vp lc gl = ret mps2)
  (H0 : Opsem.getOperandValue TD v1 lc gl = Some gvs1)
  (Hinp: mp2 @ mps2) (H1 : gv1 @ gvs1)
  (Hst: mstore TD M mp2 t gv1 align = Some M') ECs
  (Hht: wf_ECStack_head_tail maxb pinfo TD M lc 
          (List.map 
             (fun ec => let '(Opsem.mkEC f _ _ _ lc _) := ec in (f, lc)) ECs))
  (Hwf: wf_ECStack maxb pinfo TD M ECs),
  wf_ECStack maxb pinfo TD M' ECs.
Proof.
  induction ECs; simpl; intros; auto.
    destruct Hwf as [J1 [J2 J3]].
    apply wf_ECStack_head_tail_cons__inv in Hht.
    destruct Hht as [Hht1 Hht2].
    split.
      eapply impure_cmd_preserves_wf_EC_tail with (M:=M); eauto.
        destruct a. intros. subst.
        eapply mstore_preserves_wf_defs_in_tail with (mps2:=mps2)(gvs1:=gvs1)
          (v:=v1)(lc1:=lc)(vp:=vp) in Hst; eauto.
        eapply mstore_preserves_wf_lc; eauto.
    split; auto.
      destruct a. simpl in *.
      eapply mstore_preserves_wf_ECStack_head_tail 
        with (EC:=(CurFunction, Locals)); eauto.
        intros.
        apply wf_ECStack_head_tail_cons__intro; auto.
Qed.

Lemma mstore_preserves_wf_Mem : forall maxb TD M mp2 t gv1 align M' gvs1 gl
  (Hwfgl: wf_globals maxb gl) (lc:DGVMap) v1 (Hwflc: wf_lc M lc) 
  (H0 : Opsem.getOperandValue TD v1 lc gl = Some gvs1)
  (H1 : gv1 @ gvs1)
  (Hst: mstore TD M mp2 t gv1 align = Some M')
  (Hwf: wf_Mem maxb TD M),
  wf_Mem maxb TD M'.
Proof.
  intros. destruct Hwf as [J1 J2].
  assert (Mem.nextblock M = Mem.nextblock M') as EQ.
    admit. (* Mem Props *)
  rewrite EQ in *.
  split; eauto.
    intros.
    eapply mstore_preserves_mload_inv in H; eauto.
    destruct H as [G | [G | G]]; subst; eauto.
      unfold gundef in G.
      destruct (getTypeSizeInBits TD ty); tinv G.
 
      eapply operand__lt_nextblock with (M:=M) in H0; eauto.
        rewrite EQ in H0; auto.
        rewrite EQ; auto.
Qed.

Lemma mstore_preserves_wf_als : forall TD M mp2 t gv1 align M' maxb als
  (Hst: mstore TD M mp2 t gv1 align = Some M') 
  (Hwf: wf_als maxb M als),
  wf_als maxb M' als.
Proof.
  intros. destruct Hwf as [J1 J2].
  split; auto.
    intros. 
    apply J2 in H; auto.
    admit. (* Mem Props *)
Qed.

Lemma mstore_preserves_wf_ECStack_head_tail': forall maxb pinfo ECs TD M 
  gv1 align M' lc mp2 t gvs1 gl v1 (Hwfgl: wf_globals maxb gl) 
  (H0 : Opsem.getOperandValue TD v1 lc gl = Some gvs1)
  (H1 : gv1 @ gvs1)
  (Hst: mstore TD M mp2 t gv1 align = Some M') 
  (Hwf: wf_ECStack_head_tail maxb pinfo TD M lc ECs),
  wf_ECStack_head_tail maxb pinfo TD M' lc ECs.
Proof.
  intros.
  unfold wf_ECStack_head_tail, wf_ECStack_head_in_tail.
  intros.
  assert (no_alias gv1 gvsa) as J.
    eapply operand__no_alias_with__tail with (M:=M); eauto.
      apply Hwf; auto.
      rewrite <- H2.
      destruct ec0; auto.
  eapply Hwf in H3; eauto.
  destruct H3 as [[mb [J11 J12]] [J2 J3]]; subst.
  split. exists mb. split; auto. admit. (* MemProp *)
  split; auto.
    intros.
    eapply mstore_preserves_mload_inv in Hst; eauto.
    destruct Hst as [G | [G | G]]; subst; eauto.
      eapply undef_disjoint_with_runtime_alloca; eauto.
Qed.

Lemma malloc_preserves_mload_inv: forall TD M M' mb align0 gn tsz 
  (Hal : malloc TD M tsz gn align0 = ret (M', mb))
  gptr gvs1 ty al 
  (H : mload TD M' gptr ty al = ret gvs1),
  mload TD M gptr ty al = ret gvs1 \/ ret gvs1 = gundef TD ty.
Admitted.

Lemma malloc_preserves_wf_ECStack_head_tail : forall maxb pinfo ECs TD M tsz gn 
  align0 M' lc mb t id0
  (Hmlc: malloc TD M tsz gn align0 = ret (M', mb))
  (Hwf: wf_ECStack_head_tail maxb pinfo TD M lc ECs),
  wf_ECStack_head_tail maxb pinfo TD M' 
    (updateAddAL (GVsT DGVs) lc id0
        ($ blk2GV TD mb # typ_pointer t $)) ECs.
Proof.
  intros.
  unfold wf_ECStack_head_tail, wf_ECStack_head_in_tail.
  intros.
  eapply Hwf in H1; eauto.
  destruct H1 as [[mb' [J11 J12]] [J2 J3]]; subst.
  split. exists mb'. split; auto. admit. (* MemProp *)
  split.
    intros.
    destruct (id_dec id0 id1); subst.
      rewrite lookupAL_updateAddAL_eq in H1. inv H1.
      admit. (* MemProp mb'<M.next=mb *)

      rewrite <- lookupAL_updateAddAL_neq in H1; eauto.

    intros.
    eapply malloc_preserves_mload_inv in Hmlc; eauto.
    destruct Hmlc as [G | G]; subst; eauto.
      eapply undef_disjoint_with_runtime_alloca; eauto.
Qed.

Lemma malloc_preserves_wf_defs_in_tail : forall maxb pinfo TD M  
  M' als lc mb align0 gn tsz (Hal: malloc TD M tsz gn align0 = ret (M', mb))
  ids0 (Hwf: wf_defs maxb pinfo TD M lc ids0 als),
  wf_defs maxb pinfo TD M lc ids0 als ->
  wf_defs maxb pinfo TD M' lc ids0 als.
Proof.
  intros. unfold wf_defs. 
  intros gvsa Hpindom Hlkp.
  assert (Hlkp':=Hlkp).
  apply Hwf in Hlkp'; auto.
  destruct Hlkp' as [J1 J2].
  split; auto.
    clear J2.
    destruct J1 as [[mb' [J11 J12]] [J4 [gv J3]]]; subst.
    split; eauto.
    split.
      intros.
      eapply malloc_preserves_mload_inv in H0; eauto.
      destruct H0 as [G | G]; subst; eauto.
        eapply undef_disjoint_with_runtime_alloca; eauto.

      exists gv. admit. (* Mem Prop *)
Qed.

Lemma malloc_preserves_wf_lc_in_tail: forall TD M M' tsz gn align0 mb lc
  (Hmalloc: malloc TD M tsz gn align0 = ret (M', mb)) 
  (Hwf: wf_lc M lc), wf_lc M' lc.
Proof.
  unfold wf_lc.
  intros.
  admit. (* Mem Props *)
Qed.

Lemma malloc_preserves_wf_ECStack_head_tail' : forall maxb pinfo ECs TD M tsz gn 
  align0 M' lc mb 
  (Hmlc: malloc TD M tsz gn align0 = ret (M', mb))
  (Hwf: wf_ECStack_head_tail maxb pinfo TD M lc ECs),
  wf_ECStack_head_tail maxb pinfo TD M' lc ECs.
Proof.
  intros.
  unfold wf_ECStack_head_tail, wf_ECStack_head_in_tail.
  intros.
  eapply Hwf in H1; eauto.
  destruct H1 as [[mb' [J11 J12]] [J2 J3]]; subst.
  split. exists mb'. split; auto. admit. (* MemProp *)
  split; eauto.
    intros.
    eapply malloc_preserves_mload_inv in Hmlc; eauto.
    destruct Hmlc as [G | G]; subst; eauto.
      eapply undef_disjoint_with_runtime_alloca; eauto.
Qed.

Lemma malloc_preserves_wf_ECStack_in_tail : forall maxb pinfo TD M tsz gn align0 
  (Hwfpi: WF_PhiInfo pinfo) M' mb 
  (Hmlc: malloc TD M tsz gn align0 = ret (M', mb)) ECs
  (Hwf: wf_ECStack maxb pinfo TD M ECs),
  wf_ECStack maxb pinfo TD M' ECs.
Proof.
  induction ECs; simpl; intros; auto.
    destruct Hwf as [J1 [J2 J3]].
    split.
      eapply impure_cmd_preserves_wf_EC_tail with (M:=M); eauto.
        destruct a. intros. subst.
        eapply malloc_preserves_wf_defs_in_tail in Hmlc; eauto.
        eapply malloc_preserves_wf_lc_in_tail; eauto. 
    split; auto.
      destruct a. simpl in *.
      eapply malloc_preserves_wf_ECStack_head_tail'; eauto.
Qed.

Lemma malloc_preserves_wf_Mem : forall maxb TD M tsz gn align0 M' mb
  (Hmlc: malloc TD M tsz gn align0 = ret (M', mb))
  (Hwf: wf_Mem maxb TD M),
  wf_Mem maxb TD M'.
Proof.
  intros. destruct Hwf as [J1 J2].
  assert (Mem.nextblock M + 1 = Mem.nextblock M') as EQ.
    admit. (* Mem Props *)
  split.
    rewrite <- EQ.
    intros.
    eapply malloc_preserves_mload_inv in H; eauto.
    destruct H as [G | G]; subst; eauto.
      apply J1 in G. omega.

      unfold gundef in G.
      destruct (getTypeSizeInBits TD ty); tinv G.
 
    omega.
Qed.

Lemma malloc_preserves_wf_als : forall maxb TD M M' tsz gn align0 mb als
  (Hmalloc: malloc TD M tsz gn align0 = ret (M', mb)) 
  (Hwf: wf_als maxb M als),
  wf_als maxb M' (mb::als).
Proof.
  intros. destruct Hwf as [J1 J2].
  split.
    constructor; auto.
      intro J. apply J2 in J.
      admit. (* Mem Props *)

    intros. 
    simpl in H. 
    destruct H as [H | H]; subst.
      admit. (* Mem Props *)

      apply J2 in H.
      admit. (* Mem Props *)
Qed.

Lemma impure_cmd_updated_preserves_wf_EC : forall maxb pinfo TD M M' lc F B 
  als als' tmn cs c0 l1 ps1 cs1' ifs S
  (Heq: B = block_intro l1 ps1 (cs1' ++ c0 :: cs) tmn)
  (HwfS: wf_system ifs S) los nts (Heq': TD = (los, nts)) Ps
  (HMinS: moduleInSystemB (module_intro los nts Ps) S = true)
  (HFinPs: InProductsB (product_fdef F) Ps = true)
  (HBinF: blockInFdefB B F = true) id0
  (Hid : getCmdID c0 = Some id0) gv3
  (Hwfdefs: forall ids0,
              F = (PI_f pinfo) ->
              inscope_of_pc F B (c0::cs) tmn = Some ids0 ->
              wf_defs maxb pinfo TD M lc ids0 als ->
              wf_defs maxb pinfo TD M' 
                (updateAddAL (GVsT DGVs) lc id0 gv3) (id0::ids0) als')
  (Hwflc: wf_lc M lc -> wf_lc M' (updateAddAL (GVsT DGVs) lc id0 gv3)) EC
  (Heq: EC = {| Opsem.CurFunction := F;
               Opsem.CurBB := B;
               Opsem.CurCmds := c0 :: cs;
               Opsem.Terminator := tmn;
               Opsem.Locals := lc;
               Opsem.Allocas := als |})
  (HwfEC: wf_ExecutionContext maxb pinfo TD M EC),
  wf_ExecutionContext maxb pinfo TD M'
    {| Opsem.CurFunction := F;
       Opsem.CurBB := B;
       Opsem.CurCmds := cs;
       Opsem.Terminator := tmn;
       Opsem.Locals := updateAddAL (GVsT DGVs) lc id0 gv3;
       Opsem.Allocas := als' |}.
Proof.
  simpl. intros. subst.
  destruct HwfEC as [J1 J2].
  split; auto.
  destruct (fdef_dec (PI_f pinfo) F); subst; auto.
  remember (inscope_of_cmd (PI_f pinfo) 
    (block_intro l1 ps1 (cs1' ++ c0 :: cs) tmn) c0) as R1. 
  assert (HeqR1':=HeqR1).
  unfold inscope_of_cmd, inscope_of_id in HeqR1'.

  destruct R1; try solve [inversion J1].
  repeat (split; try solve [auto]).
      destruct cs; simpl_env in *.
      SSSSCase "cs = nil".
        assert (~ In (getCmdLoc c0) (getCmdsLocs cs1')) 
          as Hnotin.
          eapply preservation_helper1; eauto.

        apply inscope_of_cmd_tmn in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1' J2']].
        rewrite <- J1'.
        assert (In c0 (cs1' ++ [c0])) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc; 
          eauto.
        assert (HwfF:=HFinPs). eapply wf_system__wf_fdef in HwfF; eauto.
        rewrite Hid in J2'.
        eapply wf_defs_eq; eauto.       

      SSSSCase "cs <> nil".
        assert (NoDup (getCmdsLocs (cs1' ++ [c0] ++ [c] ++ cs))) 
          as Hnodup.
          eapply preservation_helper2; eauto.

        apply inscope_of_cmd_cmd in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1' J2']].        
        rewrite <- J1'.
        assert (In c0 (cs1' ++ [c0] ++ [c] ++ cs)) 
          as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc; 
          eauto.
        rewrite Hid in J2'. 
        eapply wf_defs_eq; eauto.
Qed.

Lemma alloca_preserves_wf_defs_at_head : forall maxb pinfo TD M  
  M' gl als lc t v
  (Hwfgl: wf_globals maxb gl) mb id0 tmn align0 cs cs1' l1 ps1 F gn tsz
  (Hal: malloc TD M tsz gn align0 = ret (M', mb)) (HwfM: wf_Mem maxb TD M)
  (Hwflc : wf_lc M lc),
  forall ids0,
   F = PI_f pinfo ->
   inscope_of_pc F
     (block_intro l1 ps1 (cs1' ++ insn_alloca id0 t v align0 :: cs) tmn)
     (insn_alloca id0 t v align0 :: cs) tmn = ret ids0 ->
   wf_defs maxb pinfo TD M lc ids0 als ->
   wf_defs maxb pinfo TD M'
     (updateAddAL (GVsT DGVs) lc id0
        ($ blk2GV TD mb # typ_pointer t $)) 
     (id0 :: ids0) (mb :: als).
Proof.
  intros. unfold wf_defs. 
  intros gvsa Hpindom Hlkp.
  destruct (id_dec id0 (PI_id pinfo)); subst.
    rewrite lookupAL_updateAddAL_eq in Hlkp.
    inv Hlkp.
    split.
      split.
        exists mb. admit. (* WF, MemProp *)
      split.
        intros.
        assert (mload TD M gptr ty al = ret gvs1 \/
                Some gvs1 = gundef TD ty) as J.
          eapply malloc_preserves_mload_inv; eauto.
        destruct J as [J | J].
          destruct HwfM as [HwfM _].
          admit. (* if gvs1 isnt ptr, done; else by HwfM *)

          eapply undef_disjoint_with_runtime_alloca; eauto.

        admit. (* MemProp by Hal. *)

      intros.
      unfold wf_non_alloca_GVs.
      destruct (id_dec id0 (PI_id pinfo)); auto.
      rewrite <- lookupAL_updateAddAL_neq in Hlk0; auto.
      admit. (* if gvs1 isnt ptr, done; else by Hwflc *)

    rewrite <- lookupAL_updateAddAL_neq in Hlkp; auto.
    simpl in Hpindom.
    destruct Hpindom as [Hpindom | Hpindom]; subst; try congruence.
    assert (Hlkp':=Hlkp).
    apply H1 in Hlkp; auto.
    destruct Hlkp as [J1 J2].
    split.
      destruct J1 as [[mb' [J31 [J32 J33]]] [J4 [gv J5]]]; subst.
      split.
        exists mb'. split; auto. simpl. auto.
      split.
        intros.
        assert (mload TD M gptr ty al = ret gvs1 \/
                Some gvs1 = gundef TD ty) as J.
          eapply malloc_preserves_mload_inv; eauto.
        destruct J as [J | J]; eauto.
          eapply undef_disjoint_with_runtime_alloca; eauto.

        exists gv. admit. (* MemProp by Hal. *)

      intros.
      unfold wf_non_alloca_GVs.
      destruct (id_dec id1 (PI_id pinfo)); auto.
      destruct (id_dec id0 id1); subst.
        rewrite lookupAL_updateAddAL_eq in Hlk0.
        inv Hlk0.
        admit. (* if gvsa isnt ptr, done; else by Hwflc *)

        rewrite <- lookupAL_updateAddAL_neq in Hlk0; auto.
        clear - Hpindom H0.
        admit. (* sdom is acyclic *)
Qed.

Lemma malloc_preserves_wf_defs_at_head : forall maxb pinfo TD M  
  M' gl als lc t v
  (Hwfgl: wf_globals maxb gl) mb id0 tmn align0 cs cs1' l1 ps1 F gn tsz
  (Hal: malloc TD M tsz gn align0 = ret (M', mb)) (HwfM: wf_Mem maxb TD M)
  (Hwflc : wf_lc M lc),
  forall ids0,
   F = PI_f pinfo ->
   inscope_of_pc F
     (block_intro l1 ps1 (cs1' ++ insn_malloc id0 t v align0 :: cs) tmn)
     (insn_alloca id0 t v align0 :: cs) tmn = ret ids0 ->
   wf_defs maxb pinfo TD M lc ids0 als ->
   wf_defs maxb pinfo TD M'
     (updateAddAL (GVsT DGVs) lc id0
        ($ blk2GV TD mb # typ_pointer t $)) 
     (id0 :: ids0) als.
Proof.
  intros. unfold wf_defs. 
  intros gvsa Hpindom Hlkp.
  destruct (id_dec id0 (PI_id pinfo)); subst.
    rewrite lookupAL_updateAddAL_eq in Hlkp.
    inv Hlkp.
    split.
      split.
        exists mb. admit. (* WF, MemProp *)
      split.
        intros.
        assert (mload TD M gptr ty al = ret gvs1 \/
                Some gvs1 = gundef TD ty) as J.
          eapply malloc_preserves_mload_inv; eauto.
        destruct J as [J | J].
          destruct HwfM as [HwfM _].
          admit. (* if gvs1 isnt ptr, done; else by HwfM *)

          eapply undef_disjoint_with_runtime_alloca; eauto.

        admit. (* MemProp by Hal. *)

      intros.
      unfold wf_non_alloca_GVs.
      destruct (id_dec id0 (PI_id pinfo)); auto.
      rewrite <- lookupAL_updateAddAL_neq in Hlk0; auto.
      admit. (* if gvs1 isnt ptr, done; else by Hwflc *)

    rewrite <- lookupAL_updateAddAL_neq in Hlkp; auto.
    simpl in Hpindom.
    destruct Hpindom as [Hpindom | Hpindom]; subst; try congruence.
    assert (Hlkp':=Hlkp).
    apply H1 in Hlkp; auto.
    destruct Hlkp as [J1 J2].
    split.
      destruct J1 as [[mb' [J31 [J32 J33]]] [J4 [gv J5]]]; subst.
      split.
        exists mb'. split; auto. simpl. auto.
      split.
        intros.
        assert (mload TD M gptr ty al = ret gvs1 \/
                Some gvs1 = gundef TD ty) as J.
          eapply malloc_preserves_mload_inv; eauto.
        destruct J as [J | J]; eauto.
          eapply undef_disjoint_with_runtime_alloca; eauto.

        exists gv. admit. (* MemProp by Hal. *)

      intros.
      unfold wf_non_alloca_GVs.
      destruct (id_dec id1 (PI_id pinfo)); auto.
      destruct (id_dec id0 id1); subst.
        rewrite lookupAL_updateAddAL_eq in Hlk0.
        inv Hlk0.
        admit. (* if gvsa isnt ptr, done; else by Hwflc *)

        rewrite <- lookupAL_updateAddAL_neq in Hlk0; auto.
        clear - Hpindom H0.
        admit. (* sdom is acyclic *)
Qed.

Lemma malloc_preserves_wf_lc: forall TD M M' tsz gn align0 mb t id0 lc
  (Hmalloc: malloc TD M tsz gn align0 = ret (M', mb)) 
  (Hwf: wf_lc M lc),
  wf_lc M' (updateAddAL (GVsT DGVs) lc id0 ($ blk2GV TD mb # typ_pointer t $)).
Proof.
  unfold wf_lc.
  intros.
  destruct (id_dec id0 id1); subst.
    rewrite lookupAL_updateAddAL_eq in H.
    admit. (* Mem Props *)

    rewrite <- lookupAL_updateAddAL_neq in H; auto.
    apply Hwf in H.
    admit. (* Mem Props *)
Qed.

Ltac simpl_ctx Hinv HwfS1 :=
  destruct Hinv as 
    [_ [HwfSystem [HmInS [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [_ [_ [l1 [ps1 [cs1' Heq1]]]]]]]] 
     [HwfEC0 HwfCall]
    ]]]]]; subst;
  fold (@OpsemPP.wf_ECStack DGVs) in HwfEC0;
  destruct HwfS1 as [[HwfEC [HwfECs Hwfht]] [Hnonup1 HwfM1]].

Lemma preservation : forall maxb pinfo cfg S1 S2 tr
  (Hinv: OpsemPP.wf_State cfg S1)
  (Hwfg: wf_globals maxb ((OpsemAux.Globals cfg)))
  (HwfPI: WF_PhiInfo pinfo) (HsInsn: Opsem.sInsn cfg S1 S2 tr)
  (HwfS1: wf_State maxb pinfo cfg S1), wf_State maxb pinfo cfg S2.
Proof.
  intros.
  (sInsn_cases (induction HsInsn) Case); destruct TD as [los nts]; simpl HwfS1.

Case "sReturn". eapply preservation_return; eauto. 
Case "sReturnVoid". admit.
Case "sBranch". admit.
Case "sBranch_uncond". admit.
Case "sBop".
  eapply preservation_pure_cmd_updated_case in HwfS1; try solve [simpl; eauto]; 
    eauto.
    eapply BOP__wf_GVs_in_EC; eauto.
      admit. (* WF *)
Case "sFBop". admit.
Case "sExtractValue". admit. 
(* tricky case, 
   we need to ensure that all extractable values cannot be aliased *)
Case "sInsertValue". admit. 
(* tricky case, 
   we need to ensure that we are not inserting aliased values *)
Case "sMalloc". 
  simpl_ctx Hinv HwfS1.
  split.
    split.
      eapply impure_cmd_updated_preserves_wf_EC; eauto.
        intros. subst.
        apply wf_EC__wf_lc in HwfEC.
        eapply malloc_preserves_wf_defs_at_head with (tmn:=tmn); eauto.
        eapply malloc_preserves_wf_lc; eauto.
    split.
      eapply malloc_preserves_wf_ECStack_in_tail in H2; eauto.
      eapply malloc_preserves_wf_ECStack_head_tail in H2; eauto.
  split.
    eapply malloc_preserves_wf_als in H2; eauto.
      simpl_env in H2.
      apply wf_als_split in H2. destruct H2; auto.
    eapply malloc_preserves_wf_Mem in H2; eauto.

Case "sFree". 
  simpl_ctx Hinv HwfS1.
  split.
    split.
      eapply impure_cmd_non_updated_preserves_wf_EC with (M:=Mem); eauto.
        intros. subst.
        eapply free_preserves_wf_defs_at_head; eauto.
          admit. (* WF PhiInfo *)
        eapply free_preserves_wf_lc; eauto.
    split.
      eapply free_preserves_wf_ECStack_in_tail in H1; eauto.
      eapply free_preserves_wf_ECStack_head_tail in H1; eauto.
  split.
    eapply free_preserves_wf_als in H1; eauto.
    eapply free_preserves_wf_Mem in H1; eauto.

Case "sAlloca". 
  simpl_ctx Hinv HwfS1.
  split.
    split.
      eapply impure_cmd_updated_preserves_wf_EC; eauto.
        intros. subst.
        apply wf_EC__wf_lc in HwfEC.
        eapply alloca_preserves_wf_defs_at_head; eauto.
        eapply malloc_preserves_wf_lc; eauto.
    split.       
      eapply malloc_preserves_wf_ECStack_in_tail in H2; eauto.
      eapply malloc_preserves_wf_ECStack_head_tail in H2; eauto.
  split.
    eapply malloc_preserves_wf_als in H2; eauto.
    eapply malloc_preserves_wf_Mem in H2; eauto.

Case "sLoad". 
  eapply preservation_pure_cmd_updated_case in HwfS1; try solve [simpl; eauto]; 
    eauto.
    destruct HwfS1 as [[[_ Hwflc] _] [_ HwfM]]. 
    eapply mload__wf_GVs_in_EC; eauto using wf_EC__wf_lc.
      admit. (* WF *)
Case "sStore". 
  simpl_ctx Hinv HwfS1.
  assert (wf_lc Mem lc) as Hwflc.
    apply wf_EC__wf_lc in HwfEC; auto.
  split.
    split.
      eapply impure_cmd_non_updated_preserves_wf_EC with (M:=Mem); eauto.
        intros. subst.
        eapply mstore_preserves_wf_defs_at_head with (gvs1:=gvs1) in H3; eauto.
          admit. (* WF PhiInfo *)
        eapply mstore_preserves_wf_lc; eauto.
    split.
      eapply mstore_preserves_wf_ECStack_in_tail with (gvs1:=gvs1) in H3; eauto.
      eapply mstore_preserves_wf_ECStack_head_tail' with (gvs1:=gvs1) in H3; 
        eauto.
  split.
    eapply mstore_preserves_wf_als in H3; eauto.
    eapply mstore_preserves_wf_Mem with (gvs1:=gvs1) in H3; eauto.

Case "sGEP". 
  eapply preservation_pure_cmd_updated_case in HwfS1; try solve [simpl; eauto]; 
    eauto.
    destruct HwfS1 as [[[_ Hwflc] _] [_ [_ HwfM]]]. 
    eapply GEP__wf_GVs_in_EC; eauto using wf_EC__wf_lc.
      admit. (* WF PI *)
      admit. (* WF *)

Case "sTrunc". admit.
Case "sExt". admit.
Case "sCast". 
  eapply preservation_pure_cmd_updated_case in HwfS1; try solve [simpl; eauto]; 
    eauto.
    destruct HwfS1 as [[[_ Hwflc] _] [_ [_ HwfM]]]. 
    eapply CAST__wf_GVs_in_EC; eauto.
      admit. (* WF PI *)
      admit. (* WF *)

Case "sIcmp". admit.
Case "sFcmp". admit.
Case "sSelect". admit. (* can return ptr *)
Case "sCall". 
Focus.
  destruct Hinv as 
    [_ [HwfSystem [HmInS [Hnonempty [
     [Hreach1 [HBinF1 [HFinPs1 [_ [_ [l1 [ps1 [cs1' Heq1]]]]]]]] 
     [HwfEC0 HwfCall]
    ]]]]]; subst.
  fold (@OpsemPP.wf_ECStack DGVs) in HwfEC0.
  destruct HwfS1 as 
    [[[Hinscope1 Hwflc1] [HwfECs Hfr2]] [Hdisjals HwfM]].
  simpl in Hdisjals.
  fold wf_ECStack in HwfECs.
  assert (InProductsB (product_fdef (fdef_intro 
    (fheader_intro fa rt fid la va) lb)) Ps = true) as HFinPs'.
    apply OpsemAux.lookupFdefViaPtr_inversion in H1.
    destruct H1 as [fn [H11 H12]].
    eapply lookupFdefViaIDFromProducts_inv; eauto.
  split; auto.
  split.
  SCase "1".     
    assert (uniqFdef (fdef_intro (fheader_intro fa rt fid la va) lb)) as Huniq.
      eapply wf_system__uniqFdef; eauto.
    assert (wf_fdef nil S (module_intro los nts Ps) 
      (fdef_intro (fheader_intro fa rt fid la va) lb)) as HwfF.
      eapply wf_system__wf_fdef; eauto.
    split.
      destruct (fdef_dec (PI_f pinfo) 
                 (fdef_intro (fheader_intro fa rt fid la va) lb)); auto.
      assert (ps'=nil) as EQ.
        eapply entryBlock_has_no_phinodes with (ifs:=nil)(s:=S); eauto.        
      subst.
      apply dom_entrypoint in H2. 
      destruct cs'.
        unfold inscope_of_tmn.
        remember ((dom_analyze (fdef_intro (fheader_intro fa rt fid la va) lb)) 
          !! l') as R.
        destruct R. simpl in H2. subst. simpl.

        eapply preservation_dbCall_case; eauto.

        unfold inscope_of_cmd, inscope_of_id.
        remember ((dom_analyze (fdef_intro (fheader_intro fa rt fid la va) lb)) 
          !! l') as R.
        destruct R. simpl. simpl in H2. subst. simpl.
        destruct (eq_atom_dec (getCmdLoc c) (getCmdLoc c)) as [|n]; 
          try solve [contradict n; auto]. 
        eapply preservation_dbCall_case; eauto.

      eapply initLocals_preserves_wf_lc; eauto.

  split.
    repeat (split; auto). 
    simpl.
    eapply initLocals_preserves_wf_ECStack_head_tail; eauto.
Unfocus.

Case "sExCall". 
  destruct HwfS1 as [[HwfEC [HwfECs Hwfht]] [Hnonup1 HwfM1]].
  assert (wf_lc Mem lc) as Hwflc.
    apply wf_EC__wf_lc in HwfEC; auto.
  unfold Opsem.exCallUpdateLocals in H5.
  destruct noret0.
    inv H5. 
    split.
      split.
        eapply callExternalProc_preserves_wf_EC; eauto.
      split.
        eapply callExternalFunction_preserves_wf_ECStack; eauto.
        eapply callExternalProc_preserves_wf_ECStack_head_tail; eauto.
    split.
      eapply callExternalFunction_preserves_wf_als; eauto.
      eapply callExternalFunction_preserves_wf_Mem; eauto.

    destruct oresult; inv H5.
    destruct ft; tinv H7.
    remember (fit_gv (los, nts) ft g) as R.
    destruct R; inv H7.
    split.
      split.
        eapply callExternalFun_preserves_wf_EC with (ca:=ca)(fv:=fv); eauto. 
      split.
        eapply callExternalFunction_preserves_wf_ECStack; eauto.
        eapply callExternalFun_preserves_wf_ECStack_head_tail; eauto. 
    split.
      eapply callExternalFunction_preserves_wf_als; eauto.
      eapply callExternalFunction_preserves_wf_Mem; eauto.
Qed.

End Promotability.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)

