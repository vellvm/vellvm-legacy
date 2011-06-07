Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "./compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import ssa_def.
Require Import ssa_lib.
Require Import List.
Require Import Arith.
Require Import tactics.
Require Import monad.
Require Import trace.
Require Import Metatheory.
Require Import genericvalues.
Require Import assoclist.
Require Import Values.
Require Import Memory.
Require Import Integers.
Require Import Coqlib.
Require Import targetdata.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import Kildall.
Require Import ssa_analysis.
Require Import ssa_static.
Require Import ssa_dynamic.

Export LLVMwf.

  Definition getCmdID' (i:cmd) : option id :=
  match i with
  | insn_bop id _ sz v1 v2 => Some id
  | insn_fbop id _ _ _ _ => Some id
  (* | insn_extractelement id typ0 id0 c1 => id *)
  (* | insn_insertelement id typ0 id0 typ1 v1 c2 => id *)
  | insn_extractvalue id typs id0 c1 => Some id
  | insn_insertvalue id typs id0 typ1 v1 c2 => Some id 
  | insn_malloc id _ _ _ => Some id
  | insn_free id _ _ => None
  | insn_alloca id _ _ _ => Some id
  | insn_load id typ1 v1 _ => Some id
  | insn_store id typ1 v1 v2 _ => None
  | insn_gep id _ _ _ _ => Some id
  | insn_trunc id _ typ1 v1 typ2 => Some id 
  | insn_ext id _ sz1 v1 sz2 => Some id
  | insn_cast id _ typ1 v1 typ2 => Some id
  | insn_icmp id cond typ v1 v2 => Some id
  | insn_fcmp id cond typ v1 v2 => Some id 
  | insn_select id v0 typ v1 v2 => Some id
  | insn_call id nr _ typ v0 paraml => if nr then None else Some id
  end.
 
Fixpoint cmds_dominates_cmd_aux (cs:cmds) (id0:id) (ctx:atoms) : option atoms :=
match cs with
| nil => None
| c1::cs' => 
    match getCmdID' c1 with
    | Some id1 =>
      if eq_atom_dec id1 id0 then 
        Some ctx 
      else cmds_dominates_cmd_aux cs' id0 ({{id1}} `union` ctx)
    | None => Some ctx
    end
end.

Definition cmds_dominates_cmd (cs:cmds) (id0:id) : option atoms :=
cmds_dominates_cmd_aux cs id0 {}. 

Fixpoint getCmdsIDs (cs:cmds) : atoms :=
match cs with
| nil => {}
| c::cs' =>
    match getCmdID' c with 
    | Some id1 => {{id1}} `union` getCmdsIDs cs'
    | None => getCmdsIDs cs'
    end
end.

Fixpoint getPhiNodesIDs' (ps: phinodes) : atoms :=
match ps with
| nil => {}
| p::ps' => 
    let id1 := getPhiNodeID p in 
    {{id1}} `union` getPhiNodesIDs' ps'
end.

Definition getBlockIDs (b:block) : atoms :=
let '(block_intro _ ps cs _) := b in
getPhiNodesIDs' ps `union` getCmdsIDs cs.

Fixpoint getArgsIDs (la:args) : atoms :=
match la with
| nil => {}
| (_,id1)::la' => {{id1}} `union` getArgsIDs la'
end.

Definition inscope_of_cmd (f:fdef) (b1:block) (c:cmd) : option atoms :=
let id0 := getCmdID c in
let '(block_intro l1 ps cs _) := b1 in
let '(fdef_intro (fheader_intro _ _ la) _) := f in
let 'dt := dom_analyze f in
let '(Dominators.mkBoundedSet els _) := AMap.get l1 dt in
match cmds_dominates_cmd cs id0 with
| None => None
| Some ids' => 
    fold_left 
      (fun (opt_ctx:option atoms) (lbl:l) =>
         match opt_ctx with
         | Some ctx =>
           match lookupBlockViaIDFromFdef f lbl with
           | None => None
           | Some b => 
               if eq_atom_dec lbl l1 then Some ctx
               else Some (getBlockIDs b `union` ctx)
           end
         | None => None
         end
      )
      (AtomSetImpl.elements els) 
      (Some (getPhiNodesIDs' ps `union` ids' `union` getArgsIDs la))
end.

Definition inscope_of_tmn (f:fdef) (b1:block) (tmn:terminator) : option atoms :=
let '(block_intro l1 ps cs _) := b1 in
let '(fdef_intro (fheader_intro _ _ la) _) := f in
let 'dt := dom_analyze f in
let '(Dominators.mkBoundedSet els _) := AMap.get l1 dt in
fold_left 
  (fun (opt_ctx:option atoms) (lbl:l) =>
     match opt_ctx with
     | Some ctx =>
       match lookupBlockViaIDFromFdef f lbl with
       | None => None
       | Some b => 
         if eq_atom_dec lbl l1 then Some ctx
         else Some (getBlockIDs b `union` ctx)
       end
     | None => None
     end
  )
  (AtomSetImpl.elements els) 
  (Some (getPhiNodesIDs' ps `union` getCmdsIDs cs `union` getArgsIDs la)).

Definition defs_dominate (f:fdef) (curb incomingb:block) (i:insn) : option atoms 
  :=
match i with
| insn_phinode p => 
    let '(block_intro _ _ _ tmn) := incomingb in
    inscope_of_tmn f incomingb tmn
| insn_cmd c => inscope_of_cmd f curb c
| insn_terminator tmn => inscope_of_tmn f curb tmn
end.

Export LLVMgv.
Export LLVMopsem.

(* FIXME: this could be the tricky part. *)
Inductive wf_genericvalue : GenericValue -> typ -> Prop :=
| wf_genericvalue_intro : forall gv t, wf_genericvalue gv t.

Inductive wf_defs : fdef -> GVMap -> ids -> Prop :=
| wf_defs_nil : forall f lc, wf_defs f lc nil
| wf_defs_cons : forall f lc id1 gv1 t1 ids',
    lookupTypViaIDFromFdef f id1 = Some t1 ->
    wf_genericvalue gv1 t1 ->
    wf_defs f lc ids' ->
    wf_defs f lc (id1::ids')
.

Definition wf_ExecutionContext (ps:list product) (ec:ExecutionContext) : Prop :=
let '(mkEC f b cs tmn lc als) := ec in
(*isReachableFromEntry f b /\*)
blockInFdefB b f = true /\
InProductsB (product_fdef f) ps = true /\
match cs with
| nil => 
    match inscope_of_tmn f b tmn with
    | Some ids => wf_defs f lc (AtomSetImpl.elements ids)
    | None => False
    end
| c::_ =>
    match inscope_of_cmd f b c with
    | Some ids => wf_defs f lc (AtomSetImpl.elements ids)
    | None => False
    end
end /\
exists l1, exists ps, exists cs',
b = block_intro l1 ps (cs'++cs) tmn.

Definition wf_call (ec:ExecutionContext) (ecs:ECStack) : Prop :=
let '(mkEC f b cs tmn lc als) := ec in
match tmn with
| insn_return _ _ _ =>
    match ecs with
    | nil => True
    | mkEC f' b' (insn_call _ _ _ _ _ _ ::_) tmn' lc' als'::ecs' => True
    | _ => False
    end
| insn_return_void _ =>
    match ecs with
    | nil => True
    | mkEC f' b' (insn_call _ true _ _ _ _ ::_) tmn' lc' als'::ecs' => True
    | _ => False
    end
| _ => True
end.

Fixpoint wf_ECStack (ps:list product) (ecs:ECStack) : Prop :=
match ecs with
| nil => True
| ec::ecs' => wf_ExecutionContext ps ec /\ wf_ECStack ps ecs' /\ wf_call ec ecs'
end.

Definition wf_State (S:State) : Prop :=
let '(mkState s (los, nts) ps ecs _ _ _) := S in
wf_system nil s /\
moduleInSystemB (module_intro los nts ps) s = true /\
wf_ECStack ps ecs.

Lemma inscope_of_cmd_tmn : forall f l2 ps2 cs2' c' tmn' ids1,
Some ids1 = inscope_of_cmd f (block_intro l2 ps2 (cs2'++[c']) tmn') c' ->
exists ids2, 
  Some ids2 = inscope_of_tmn f (block_intro l2 ps2 (cs2'++[c']) tmn') tmn' /\
  match getCmdID' c' with
  | Some id1 => {{id1}} `union` ids1 [=] ids2
  | None => ids1 [=] ids2
  end.
Admitted.

Lemma wf_defs_updateAddAL : forall g TD Mem' Result lc gl F' lc' t ids2 i1,
  ret g = getOperandValue TD Mem' Result lc gl ->
  wf_defs F' lc' (AtomSetImpl.elements t) ->
  union (singleton i1) t[=]ids2 ->
  wf_defs F' (updateAddAL GenericValue lc' i1 g) (AtomSetImpl.elements ids2).
Admitted.

Lemma wf_defs_eq : forall ids1 ids2 F' lc',
  ids1 [=] ids2 ->
  wf_defs F' lc' (AtomSetImpl.elements ids1) ->
  wf_defs F' lc' (AtomSetImpl.elements ids2).
Admitted.

Lemma inscope_of_cmd_cmd : forall f l2 ps2 cs2' c' c cs' tmn' ids1,
Some ids1 = inscope_of_cmd f (block_intro l2 ps2 (cs2'++[c']++[c]++cs') tmn') c' 
  ->
exists ids2, 
  Some ids2 = 
    inscope_of_cmd f (block_intro l2 ps2 (cs2'++[c']++[c]++cs') tmn') c /\
  match getCmdID' c' with
  | Some id1 => {{id1}} `union` ids1 [=] ids2
  | None => ids1 [=] ids2
  end.
Admitted.

Lemma inscope_of_tmn_br : forall F l0 ps cs bid l1 l2 ids0 l' ps' cs' tmn' Cond 
  c TD Mem0 gl lc,
Some ids0 = inscope_of_tmn F (block_intro l0 ps cs (insn_br bid Cond l1 l2)) 
  (insn_br bid Cond l1 l2) ->
getOperandValue TD Mem0 Cond lc gl = ret c ->
Some (block_intro l' ps' cs' tmn') =
       (if isGVZero TD c
        then lookupBlockViaLabelFromFdef F l2
        else lookupBlockViaLabelFromFdef F l1) ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  AtomSetImpl.diff ids0' (getPhiNodesIDs' ps') [<=] ids0.
Admitted.

Lemma wf_defs_br : forall TD Mem0 Cond lc gl c l' ps' cs' lc' F l1 l2 bid tmn'
  (H : getOperandValue TD Mem0 Cond lc gl = ret c)
  (H0 : ret block_intro l' ps' cs' tmn' =
       (if isGVZero TD c
        then lookupBlockViaLabelFromFdef F l2
        else lookupBlockViaLabelFromFdef F l1))
  (l3 : l)
  (ps3 : phinodes)
  (cs3' : list cmd)
  (H1 : switchToNewBasicBlock TD Mem0 (block_intro l' ps' cs' tmn')
         (block_intro l3 ps3 (cs3' ++ nil) (insn_br bid Cond l1 l2)) gl lc =
       ret lc')
  (t : atoms)
  (Hinscope1 : wf_defs F lc (AtomSetImpl.elements t))
  (ids0' : atoms)
  (HeqR12 : AtomSetImpl.diff ids0' (getPhiNodesIDs' ps')[<=]t),
  wf_defs F lc' (AtomSetImpl.elements ids0').
Admitted.

Lemma inscope_of_tmn_br_uncond : forall F l3 ps cs bid ids0 l' ps' cs' tmn' l0,
Some ids0 = inscope_of_tmn F (block_intro l3 ps cs (insn_br_uncond bid l0)) 
  (insn_br_uncond bid l0) ->
Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  AtomSetImpl.diff ids0' (getPhiNodesIDs' ps') [<=] ids0.
Admitted.

Lemma wf_defs_br_uncond : forall lc l' ps' cs' lc' F bid tmn' gl l0 TD 
  Mem0
  (H0 : ret block_intro l' ps' cs' tmn' =lookupBlockViaLabelFromFdef F l0)
  (l3 : l)
  (ps3 : phinodes)
  (cs3' : list cmd)
  (H1 : switchToNewBasicBlock TD Mem0 (block_intro l' ps' cs' tmn')
         (block_intro l3 ps3 (cs3' ++ nil) (insn_br_uncond bid l0)) gl lc =
       ret lc')
  (t : atoms)
  (Hinscope1 : wf_defs F lc (AtomSetImpl.elements t))
  (ids0' : atoms)
  (HeqR12 : AtomSetImpl.diff ids0' (getPhiNodesIDs' ps')[<=]t),
  wf_defs F lc' (AtomSetImpl.elements ids0').
Admitted.


Lemma wf_system__wf_insn : forall l1 ps1 cs1 tmn1 f ps los nts s ifs,
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true -> 
  InProductsB (product_fdef f) ps = true ->
  moduleInSystemB (module_intro los nts ps) s = true ->
  wf_system ifs s ->
  wf_insn ifs s (module_intro los nts ps) f (block_intro l1 ps1 cs1 tmn1) 
    (insn_terminator tmn1).
Admitted.

Lemma preservation : forall S1 S2 tr,
  dsInsn S1 S2 tr -> wf_State S1 -> wf_State S2.
Proof.
  intros S1 S2 tr HdsInsn HwfS1.
  (dsInsn_cases (induction HdsInsn) Case); destruct TD as [los nts].
Focus.
Case "dsReturn".
  destruct HwfS1 as 
    [HwfSystem [HmInS [
     [HBinF1 [HFinPs1 [Hinscope1 [l1 [ps1 [cs1' Heq1]]]]]] 
     [
       [
         [HBinF2 [HFinPs2 [Hinscope2 [l2 [ps2 [cs2' Heq2]]]]]] 
         [HwfEC HwfCall]
       ]
       HwfCall'
     ]
    ]]]; subst.
  remember (inscope_of_cmd F' (block_intro l2 ps2 (cs2' ++ c' :: cs') tmn') c')
    as R2.
  destruct R2; try solve [inversion Hinscope2].
  remember (inscope_of_tmn F
             (block_intro l1 ps1 (cs1' ++ nil)(insn_return rid RetTy Result))
             (insn_return rid RetTy Result)) as R1. 
  destruct R1; try solve [inversion Hinscope1].
  split; auto.
  split; auto.
  SCase "1".
    split; auto.
    split; auto.  
    split; auto. 
    split. 
    SSCase "1.1".
      destruct cs'; simpl_env in *.
      clear - HeqR2 Hinscope2 H1 H.
      SSSCase "1.1.1".
        apply inscope_of_cmd_tmn in HeqR2.
        destruct HeqR2 as [ids2 [J1 J2]].        
        rewrite <- J1.
        remember (getCmdID' c') as R.
        destruct c'; try solve [inversion H].
        unfold returnUpdateLocals in H1. simpl in H1.
        destruct R.
          destruct n; inv HeqR.
          remember (getOperandValue (los,nts) Mem' Result lc gl) as R1.
          destruct R1; inv H1.
          eapply wf_defs_updateAddAL; eauto.

          destruct n; inv HeqR. inv H1.
          eapply wf_defs_eq; eauto. 
        
      SSSCase "1.1.2".
        apply inscope_of_cmd_cmd in HeqR2.
        destruct HeqR2 as [ids2 [J1 J2]].        
        rewrite <- J1.
        remember (getCmdID' c') as R.
        destruct c'; try solve [inversion H].
        unfold returnUpdateLocals in H1. simpl in H1.
        destruct R.
          destruct n; inv HeqR.
          remember (getOperandValue (los,nts) Mem' Result lc gl) as R1.
          destruct R1; inv H1.
          eapply wf_defs_updateAddAL; eauto.

          destruct n; inv HeqR. inv H1.
          eapply wf_defs_eq; eauto. 
    SSCase "1.2".
      exists l2. exists ps2. exists (cs2'++[c']).   
      simpl_env. auto.
Unfocus.

Focus.
Case "dsReturnVoid".
  destruct HwfS1 as 
    [HwfSystem [HmInS [
     [HBinF1 [HFinPs1 [Hinscope1 [l1 [ps1 [cs1' Heq1]]]]]] 
     [
       [
         [HBinF2 [HFinPs2 [Hinscope2 [l2 [ps2 [cs2' Heq2]]]]]] 
         [HwfEC HwfCall]
       ]
       HwfCall'
     ]
    ]]]; subst.
  remember (inscope_of_cmd F' (block_intro l2 ps2 (cs2' ++ c' :: cs') tmn') c')
    as R2.
  destruct R2; try solve [inversion Hinscope2].
  remember (inscope_of_tmn F
             (block_intro l1 ps1 (cs1' ++ nil)(insn_return_void rid))
             (insn_return_void rid)) as R1. 
  destruct R1; try solve [inversion Hinscope1].
  split; auto.
  split; auto.
  SCase "1".
    split; auto.
    split; auto.
    split; auto.
    split.   
    SSCase "1.1".
      destruct cs'; simpl_env in *.
      clear - HeqR2 Hinscope2 H HwfCall'.
      SSSCase "1.1.1".
        apply inscope_of_cmd_tmn in HeqR2.
        destruct HeqR2 as [ids2 [J1 J2]].        
        rewrite <- J1.
        remember (getCmdID' c') as R.
        destruct c'; try solve [inversion H].
        destruct n; inversion HwfCall'.
        simpl in HeqR. subst R.
        eapply wf_defs_eq; eauto. 
        
      SSSCase "1.1.2".
        apply inscope_of_cmd_cmd in HeqR2.
        destruct HeqR2 as [ids2 [J1 J2]].        
        rewrite <- J1.
        remember (getCmdID' c') as R.
        destruct c'; try solve [inversion H].
        destruct n; inversion HwfCall'.
        simpl in HeqR. subst R.
        eapply wf_defs_eq; eauto. 

    SSCase "1.2".
      exists l2. exists ps2. exists (cs2'++[c']).   
      simpl_env. auto.
Unfocus.

Focus.
Case "dsBranch".
  destruct HwfS1 as 
    [HwfSystem [HmInS [
     [HBinF1 [HFinPs1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]] 
     [HwfEC _]]]
    ]; subst.
  remember (inscope_of_tmn F
             (block_intro l3 ps3 (cs3' ++ nil)(insn_br bid Cond l1 l2))
             (insn_br bid Cond l1 l2)) as R1. 
  destruct R1; try solve [inversion Hinscope1].
  split; auto.
  split; auto.
  split; auto.
  SCase "1".
    split. 
      clear - H0. admit. (* static *)
    split; auto.
    split.
      clear - H0 HeqR1 H1 Hinscope1 H.
      eapply inscope_of_tmn_br in HeqR1; eauto.
      destruct HeqR1 as [ids0' HeqR1].
      destruct cs'.
        destruct HeqR1 as [HeqR11 HeqR12]. 
        rewrite <- HeqR11.
        eapply wf_defs_br; eauto.

        destruct HeqR1 as [HeqR11 HeqR12]. 
        rewrite <- HeqR11.
        eapply wf_defs_br; eauto.

      exists l'. exists ps'. exists nil. simpl_env. auto.
  split; auto.
    admit. (* need a stronger wf_call that considers rets at all blocks *)    
Unfocus.

Focus.
Case "dsBranch_uncond".
  destruct HwfS1 as 
    [HwfSystem [HmInS [
     [HBinF1 [HFinPs1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]] 
     [HwfEC _]]]
    ]; subst.
  remember (inscope_of_tmn F
             (block_intro l3 ps3 (cs3' ++ nil)(insn_br_uncond bid l0))
             (insn_br_uncond bid l0)) as R1. 
  destruct R1; try solve [inversion Hinscope1].
  split; auto.
  split; auto.
  split; auto.
  SCase "1".
    split. clear - H0. admit. (* static *)
    split; auto.
    split.
      clear - H0 HeqR1 Hinscope1 H.
      eapply inscope_of_tmn_br_uncond with (cs':=cs')(l':=l')(ps':=ps')
        (tmn':=tmn') in HeqR1; eauto.
      destruct HeqR1 as [ids0' HeqR1].
      destruct cs'.
        destruct HeqR1 as [HeqR11 HeqR12]. 
        rewrite <- HeqR11.
        eapply wf_defs_br_uncond; eauto.

        destruct HeqR1 as [HeqR11 HeqR12]. 
        rewrite <- HeqR11.
        eapply wf_defs_br_uncond; eauto.

      exists l'. exists ps'. exists nil. simpl_env. auto.
  split; auto.
    admit. (* need a stronger wf_call that considers rets at all blocks *)    
Unfocus.

Focus.
Case "dsBop".
  destruct HwfS1 as 
    [HwfSystem [HmInS [
     [HBinF1 [HFinPs1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]
     [HwfEC HwfCall]]]
    ]; subst.
  remember (inscope_of_cmd F
             (block_intro l3 ps3 (cs3' ++ insn_bop id0 bop0 sz0 v1 v2 :: cs) tmn)
             (insn_bop id0 bop0 sz0 v1 v2)) as R1. 
  destruct R1; try solve [inversion Hinscope1].
  split; auto.
  split; auto.
  split.
  SCase "1".
    split; auto.
    split; auto.
    split.  
    SSCase "1.1".
      destruct cs; simpl_env in *.
      clear - HeqR1 Hinscope1 H.
      SSSCase "1.1.1".
        apply inscope_of_cmd_tmn in HeqR1.
        destruct HeqR1 as [ids2 [J1 J2]].        
        rewrite <- J1.
        apply BOP_inversion in H.
        admit. (* need to prove that gv3 is wf-typed. *)
        
      SSSCase "1.1.2".
        apply inscope_of_cmd_cmd in HeqR1.
        destruct HeqR1 as [ids2 [J1 J2]].        
        rewrite <- J1.
        admit. (* need to prove that gv3 is wf-typed. *)

    SSCase "1.2".
      exists l3. exists ps3. exists (cs3'++[insn_bop id0 bop0 sz0 v1 v2]).   
      simpl_env. auto.
  split; auto.
Unfocus.

Case "dsFBop". admit.
Case "dsExtractValue". admit.
Case "dsInsertValue". admit.
Case "dsMalloc". admit.
Case "dsFree". admit.
Case "dsAlloca". admit.
Case "dsLoad". admit.
Case "dsStore". admit.
Case "dsGEP". admit.
Case "dsTrunc". admit.
Case "dsExt". admit.
Case "dsCast". admit.
Case "dsIcmp". admit.
Case "dsFcmp". admit.
Case "dsSelect". admit.

Focus.
Case "dsCall".
  destruct HwfS1 as [HwfSys [HmInS [HwfEC [HwfECs HwfCall]]]].
  split; auto.
  split; auto.
  split.
  SCase "1".
    split. admit. (* static *)
    split. admit. (* static *)
    split.  
      admit. (* need to prove that initial state is good! *)
    exists l'. exists ps'. exists nil. simpl_env. auto.
  split.
  SCase "2".
    split; auto.
  SCase "3".
    simpl.  
    destruct tmn'; auto.
      admit. (* static: void cannot be assigned as a call ret. *)
Unfocus.

Case "dsExCall". admit.
Qed.

Lemma state_tmn_typing : forall ifs s m f b tmn1 defs id1 lc,
  wf_insn ifs s m f b (insn_terminator tmn1) ->
  Some defs = inscope_of_tmn f b tmn1 ->
  wf_defs f lc (AtomSetImpl.elements defs) ->
  In id1 (getInsnOperands (insn_terminator tmn1)) ->
  exists t, exists gv, lookupAL _ lc id1 = Some gv /\ wf_genericvalue gv t.
Proof.
  intros ifs s m f b tmn1 defs id1 lc HwfInstr Hinscope HwfDefs HinOps.
  inv HwfInstr.
Case "ret".
  unfold getInsnOperands, getTerminatorOperands, getValueIDs in HinOps.
  destruct value5 as [vid | vc]; try solve [inversion HinOps].
  simpl in HinOps. 
  destruct HinOps as [HinOps | HinOps]; try solve [inversion HinOps].
  subst.
  inv H7.
  simpl in H6. unfold getValueIDs in H6. simpl in H6.
  destruct id_list; inv H6.
  simpl in H8.
  inv H8. clear H13. 
  inv H7.             
  assert (isBindingInsn (lookupBindingViaIDFromFdef f i0) = ret insn') as J.
    admit.
  assert (J':=J).
  apply H14 in J'. clear H14.
  inv J'.
  clear H8.
  unfold isPhiNode in H11.
  simpl in H11.
  assert (notT (false = true)) as J'. 
    intro J2. inversion J2.
  apply H14 in J'. clear H14.
  clear - J J' HwfDefs Hinscope H0.
  assert (i0 `in` defs) as J1.
    admit.
  admit.
Admitted.

Lemma state_cmd_typing : forall ifs s m f b c defs id1 lc,
  wf_insn ifs s m f b (insn_cmd c) ->
  Some defs = inscope_of_cmd f b c ->
  wf_defs f lc (AtomSetImpl.elements defs) ->
  In id1 (getInsnOperands (insn_cmd c)) ->
  exists t, exists gv, lookupAL _ lc id1 = Some gv /\ wf_genericvalue gv t.
Admitted.


Lemma wf_system__blockInFdefB__wf_block : forall b f ps los nts s ifs,
  blockInFdefB b f = true -> 
  InProductsB (product_fdef f) ps = true ->
  moduleInSystemB (module_intro los nts ps) s = true ->
  wf_system ifs s ->
  wf_block ifs s (module_intro los nts ps) f b.
Admitted.

Lemma wf_system__lookup__wf_block : forall b f l0 ps los nts s ifs,
  Some b = lookupBlockViaLabelFromFdef f l0 ->
  InProductsB (product_fdef f) ps = true ->
  moduleInSystemB (module_intro los nts ps) s = true ->
  wf_system ifs s ->
  wf_block ifs s (module_intro los nts ps) f b.
Admitted.


Lemma wf_operand_list__wf_operand : forall id_list fdef5 block5 insn5 id_ n,
  wf_operand_list (make_list_fdef_block_insn_id (map_list_id
    (fun id_ : id => (fdef5, block5, insn5, id_)) id_list)) ->
  nth_list_id n id_list = Some id_ ->
  wf_operand fdef5 block5 insn5 id_.
Proof.
  induction id_list; intros fdef5 block5 insn5 id_ n Hwfops Hnth.
    destruct n; inversion Hnth.

    simpl in Hwfops.
    inv Hwfops.
    destruct n; inv Hnth; eauto.
Qed.        


Lemma getValueViaLabelFromValuels__getInsnOperands : forall
  (lc : GVMap)
  (l1 : l)
  (i1 : id)
  (t0 : typ)
  (vid : id)
  (value_l_id_block_list : list_value_l_id_block)
  (J : getValueViaLabelFromValuels
        (make_list_value_l
           (map_list_value_l_id_block
              (fun (value_ : value) (l_ : l) (_ : id) (_ : block) =>
               (value_, l_)) value_l_id_block_list)) l1 = 
      ret value_id vid)
  (id_list : list_id)
  (H10 : getInsnOperands
          (insn_phinode
             (insn_phi i1 t0
                (make_list_value_l
                   (map_list_value_l_id_block
                      (fun (value_ : value) (l_ : l) (_ : id) (_ : block) =>
                       (value_, l_)) value_l_id_block_list)))) =
        unmake_list_id id_list),
  exists n, nth_list_id n id_list = Some vid.
Proof.
  intros.
  generalize dependent id_list.
  induction value_l_id_block_list; intros; simpl in *.
    inversion J.

    destruct (l0 == l1); subst.
      inv J; simpl in *.
      destruct id_list; inv H10.
        exists 0%nat. auto.

      destruct v.
        destruct id_list; inv H10.
          apply IHvalue_l_id_block_list with (id_list:=id_list) in J; eauto.
          destruct J as [n' J].
          destruct (i3 == vid); subst.
            exists 0%nat. simpl. auto.
            exists (S n'). simpl. auto.

          apply IHvalue_l_id_block_list with (id_list:=id_list) in J; eauto.
Qed.


Lemma wf_value_list__wf_value : forall
  (s : system)
  (f : fdef)
  (lc : GVMap)
  (l1 : l)
  (t0 : typ)
  (vid : id)
  (value_l_id_block_list : list_value_l_id_block)
  (H2 : wf_value_list
         (make_list_system_fdef_value_typ
            (map_list_value_l_id_block
               (fun (value_ : value) (_ : l) (_ : id) (_ : block) =>
                (s, f, value_, t0)) value_l_id_block_list)))
  (J : getValueViaLabelFromValuels
        (make_list_value_l
           (map_list_value_l_id_block
              (fun (value_ : value) (l_ : l) (_ : id) (_ : block) =>
               (value_, l_)) value_l_id_block_list)) l1 = 
      ret value_id vid),
  wf_value s f (value_id vid) t0.
Proof.
  intros.
  induction value_l_id_block_list; simpl in *.
    inversion J.
    
    inv H2.
    destruct (l0==l1); subst; eauto.
      inv J. auto.
Qed.        


Lemma wf_phinodes__getIncomingValuesForBlockFromPHINodes : forall
  (s : system)
  (los : layouts)
  (nts : namedts)
  (ps : list product)
  (f : fdef)
  (i0 : id)
  (l0 : l)
  (lc : GVMap)
  (gl : GVMap)
  (M : mem)
  (t : atoms)
  l1 ps1 cs1
  (HeqR : ret t = inscope_of_tmn f 
    (block_intro l1 ps1 cs1 (insn_br_uncond i0 l0)) (insn_br_uncond i0 l0))
  (Hinscope : wf_defs f lc (AtomSetImpl.elements t))
  (ps' : phinodes)
  (cs' : cmds)
  (tmn' : terminator)
  ps2
  (HbInF : wf_block nil s (module_intro los nts ps) f 
             (block_intro l1 ps1 cs1 (insn_br_uncond i0 l0)))
  (H8 : wf_phinodes nil s (module_intro los nts ps) f
         (block_intro l0 ps' cs' tmn') ps2)
  (Hin: exists ps1, ps' = ps1 ++ ps2),
   exists RVs : list (id * GenericValue),
     getIncomingValuesForBlockFromPHINodes (los, nts) M ps2 
       (block_intro l1 ps1 cs1 (insn_br_uncond i0 l0)) gl lc =
       ret RVs.
Proof.
  intros.
        induction ps2; simpl.
          exists nil. auto.

          destruct a.
          assert (exists v, getValueViaLabelFromValuels l2 l1 = Some v) as J.
            admit. (*wf*)
          destruct J as [v J].
          rewrite J.
          destruct v as [vid | vc].
            inv H8.
            assert (exists gv1, lookupAL GenericValue lc vid = Some gv1) as J1.
              Focus.
              inv H6.              
              inv H23.
              eapply getValueViaLabelFromValuels__getInsnOperands in H10; eauto.
              destruct H10 as [n H10].
              eapply wf_operand_list__wf_operand in H12; eauto.
              assert (HwfV:=J).
              eapply wf_value_list__wf_value in HwfV; eauto.
              clear - H10 HeqR Hinscope H12 J HwfV H15.
              inv H12.  
              assert (isBindingInsn (lookupBindingViaIDFromFdef f vid) = 
                ret insn') as HBind.
                admit.
              assert (HwfSSA:=HBind).
              apply H6 in HwfSSA. clear H6.
              inv HwfSSA. clear H7.
              unfold isPhiNode in H6.
              simpl in H6.
              destruct H6 as [J1 [J2 J3]]; auto.
              assert (l'' = l1) as EQ.
                clear - H15 J J1 HBind.
                admit. (* incoming edges are identical. *)
              subst.
              assert (block'' = 
                block_intro l1 ps1 (cs1 ++ nil) (insn_br_uncond i0 l0)) as EQ.
                clear - J2. admit. (* block IDs are unique. *)
              subst.
              assert (getInsnID insn' = vid) as EQ.
                clear - HBind. admit.
              subst.
              clear - J3 Hinscope HeqR H2.
              admit. (* ?!?!?!? *)
              Unfocus.

            destruct J1 as [gv1 J1].
            rewrite J1. 
            apply IHps2 in H7.
              destruct H7 as [RVs H7].
              rewrite H7. 
              exists ((i1, gv1) :: RVs). auto.

              destruct Hin as [ps3 Hin]. subst.
              exists (ps3++[insn_phi i1 t0 l2]).
              simpl_env. auto.

            admit. (* constant *)
Qed.

Lemma progress : forall S1,
  wf_State S1 -> 
    ds_isFinialState S1 = true \/ exists S2, exists tr, dsInsn S1 S2 tr.
Proof.
  intros S1 HwfS1.
  destruct S1 as [s [los nts] ps ecs gl fs M].
  destruct HwfS1 as [HwfSys1 [HmInS1 HwfECs]].
  destruct ecs.
    admit. (* we should rule out this case. *)

  destruct e as [f b cs tmn lc als].
  destruct HwfECs as [[HbInF [HfInPs [Hinscope [l1 [ps1 [cs1 Heq]]]]]] 
                      [HwfECs HwfCall]].
  subst b.
  destruct cs.
  Case "cs=nil".
    remember (inscope_of_tmn f (block_intro l1 ps1 (cs1 ++ nil) tmn) tmn) as R.
    destruct R; try solve [inversion Hinscope].
    destruct tmn.
    SCase "tmn=ret".
      simpl in HwfCall.
      destruct ecs.
        simpl; auto.      

        right.
        destruct e as [f' b' cs' tmn' lc' als'].
        destruct cs'; try solve [inversion HwfCall].
        destruct c; try solve [inversion HwfCall]. clear HwfCall.
        assert (exists M', free_allocas (los,nts) M als = Some M') as J.
          admit.
        destruct J as [M' J].
        assert (exists lc'', 
          returnUpdateLocals (los,nts) M' (insn_call i1 n t1 t2 v0 p) v lc lc' gl
            = Some lc'') as Hretup.
          unfold returnUpdateLocals. simpl.
          destruct n.
            exists lc'. auto.
            
            destruct v as [vid | vc].
              assert (HwfInstr:=HbInF).
              eapply wf_system__wf_insn in HwfInstr; eauto.
              assert (exists t, exists gv, lookupAL _ lc vid = Some gv /\ 
                wf_genericvalue gv t) as Hlkup.
                assert (In vid (getInsnOperands (insn_terminator 
                  (insn_return i0 t0 (value_id vid))))) as HinOps.
                  simpl. auto.
                eapply state_tmn_typing in HwfInstr; eauto.

              destruct Hlkup as [gt [gv [Hlkup Hwfgv]]].
              simpl.
              rewrite Hlkup. exists (updateAddAL GenericValue lc' i1 gv). auto.

              admit. (* what if a constant is stuck~? if int2ptr is not allowed,
                        we should prove this, because globals are not changed!
                      *)
          
            destruct Hretup as [lc'' Hretup].
            exists (mkState s (los, nts) ps ((mkEC f' b' cs' tmn' lc'' als')::
              ecs) gl fs M').
            exists trace_nil.
            eauto.  

    SCase "tmn=ret void". admit.
    SCase "tmn=br". admit.
    SCase "tmn=br_uncond". 
      right.
      assert (exists ps', exists cs', exists tmn',
        Some (block_intro l0 ps' cs' tmn') = lookupBlockViaLabelFromFdef f l0) 
          as HlkB.
        admit. (* wf *)
      destruct HlkB as [ps' [cs' [tmn' HlkB]]].
      assert (exists RVs, 
        getIncomingValuesForBlockFromPHINodes (los, nts) M ps'
          (block_intro l1 ps1 (cs1 ++ nil) (insn_br_uncond i0 l0)) gl lc =
        Some RVs) as J.
        eapply wf_system__blockInFdefB__wf_block in HbInF; eauto.
        eapply wf_system__lookup__wf_block in HlkB; eauto.
        clear - HeqR Hinscope HbInF HlkB.
        inv HlkB. clear H9 H10 H7.
        eapply wf_phinodes__getIncomingValuesForBlockFromPHINodes; eauto.      
          exists nil. auto.

      destruct J as [RVs J].
      assert (exists lc', switchToNewBasicBlock (los, nts) M
        (block_intro l0 ps' cs' tmn') 
        (block_intro l1 ps1 (cs1 ++ nil) (insn_br_uncond i0 l0)) gl lc = 
          Some lc') as Hswitch.
        unfold switchToNewBasicBlock. simpl.
        rewrite J. 
        exists (updateValuesForNewBlock RVs lc). auto.
      destruct Hswitch as [lc' Hswitch].
      exists (mkState s (los, nts) ps 
              ((mkEC f (block_intro l0 ps' cs' tmn') cs' tmn' lc' als)
              ::ecs) gl fs M).
      exists trace_nil. eauto.

    SCase "tmn=unreachable". admit.

  Case "cs<>nil".
    admit.
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)
