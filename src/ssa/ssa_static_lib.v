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
Require Import alist.
Require Import Values.
Require Import Memory.
Require Import Integers.
Require Import Coqlib.
Require Import targetdata.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import Kildall.
Require Import ssa_static.
Require Import ssa_dynamic.
Require Import ssa_props.
Require Import ssa_analysis.

Export LLVMwf.
Export AtomSet.

(********************************************)
(** * Inversion of well-formedness *)

Lemma getEntryBlock_inv : forall 
  (bs : blocks)
  (l3 : l)
  (l' : l)
  (ps : phinodes)
  (cs : cmds)
  (tmn : terminator)
  (fh : fheader)
  (ifs : intrinsic_funs)
  (s : system)
  (m : module)
  (HwfF : wf_fdef ifs s m (fdef_intro fh bs))
  (HBinF : InBlocksB (block_intro l3 ps cs tmn) bs = true)
  (a : atom)
  (Hsucc : In l' (successors_terminator tmn))
  ps1 cs1 tmn1
  (H : getEntryBlock (fdef_intro fh bs) = ret block_intro a ps1 cs1 tmn1),
  l' <> a.
Proof.
  intros.  
   destruct (eq_atom_dec l' a); subst; auto.
   inv HwfF.
   simpl in H12.
   rewrite H in H7. inv H7.
   clear - H12 Hsucc HBinF.
   induction bs; simpl in *.
     inversion HBinF.
  
     apply orb_prop in HBinF.          
     destruct HBinF as [HBinF | HBinF].
       apply blockEqB_inv in HBinF; subst.
       simpl in H12.
       destruct tmn; try solve [inversion Hsucc].
         unfold hasNonePredecessor in H12.
         unfold predOfBlock in H12. simpl in H12.  
         simpl in Hsucc. 
         destruct Hsucc as [Hsucc | [Hsucc | Hsucc]]; subst; 
           try inversion Hsucc.
  
           destruct (@lookupAL_update_udb_eq (update_udb nil l3 l1) l3 a)
             as [re [Hlk Hin]]. 
           apply lookupAL_genBlockUseDef_blocks_spec with (bs:=bs) in Hlk.
           destruct Hlk as [re' [Hlk Hinc]].
           rewrite Hlk in H12.
           destruct re'; inversion H12.
           apply Hinc in Hin. inversion Hin.
  
           destruct (@lookupAL_update_udb_eq nil l3 a) as [re [Hlk Hin]].
           apply lookupAL_update_udb_spec with (l1:=l3)(l2:=l0) in Hlk.
           destruct Hlk as [re1 [Hlk Hinc1]].
           apply lookupAL_genBlockUseDef_blocks_spec with (bs:=bs) in Hlk.  
           destruct Hlk as [re2 [Hlk Hinc2]].
           rewrite Hlk in H12.
           destruct re2; inversion H12.
           apply Hinc1 in Hin. 
           apply Hinc2 in Hin. 
           inversion Hin.
  
         unfold hasNonePredecessor in H12.
         unfold predOfBlock in H12. simpl in H12.  
         simpl in Hsucc. 
         destruct Hsucc as [Hsucc | Hsucc]; subst; try inversion Hsucc.
           destruct (@lookupAL_update_udb_eq nil l3 a) as [re [Hlk Hin]]. 
           apply lookupAL_genBlockUseDef_blocks_spec with (bs:=bs) in Hlk.
           destruct Hlk as [re' [Hlk Hinc]].
           rewrite Hlk in H12.
           destruct re'; inversion H12.
           apply Hinc in Hin. inversion Hin.
     apply hasNonPredecessor__mono in H12; eauto.
Qed.

Lemma wf_modules__wf_module : forall ifs S ms m,
  wf_modules ifs S ms -> 
  moduleInSystemB m ms ->
  wf_module ifs S m.
Proof.
  induction ms; intros m HwfS HMinS; simpl in *.
    inv HMinS.

    inv HwfS.
    apply orb_prop in HMinS.
    inv HMinS; auto.
      apply moduleEqB_inv in H.
      subst. auto.
Qed.

Lemma wf_prods__wf_prod : forall ifs S M Ps P,
  wf_prods ifs S M Ps ->
  InProductsB P Ps = true ->
  wf_prod ifs S M P.
Proof.
  induction Ps; intros P HwfPs HPinPs.
    inv HPinPs.

    inv HwfPs.
    simpl in HPinPs.
    apply orb_prop in HPinPs.
    inv HPinPs; eauto.
      apply productEqB_inv in H.
      subst. auto.
Qed.

Lemma wf_system__wf_fdef : forall ifs S los nts Ps f,
  wf_system ifs S -> 
  moduleInSystemB (module_intro los nts Ps) S = true ->
  InProductsB (product_fdef f) Ps = true ->
  wf_fdef ifs S (module_intro los nts Ps) f.
Proof.
  intros ifs S los nts Ps f HwfS HMinS HPinM.
  inv HwfS. 
  eapply wf_modules__wf_module in HMinS; eauto.
  inv HMinS.
  eapply wf_prods__wf_prod in H8; eauto.
  inv H8; auto.
Qed.

Lemma wf_system__uniqFdef : forall ifs S los nts Ps f,
  wf_system ifs S -> 
  moduleInSystemB (module_intro los nts Ps) S = true ->
  InProductsB (product_fdef f) Ps = true ->
  uniqFdef f.
Proof.
  intros.
  inv H.
  apply uniqSystem__uniqFdef with (S:=S)(M:=module_intro los nts Ps); auto.
  unfold productInSystemModuleB, productInModuleB, is_true.  
  apply andb_true_iff; auto.
Qed.

Lemma wf_blocks__wf_block : forall ifs s m f bs b,
  wf_blocks ifs s m f bs -> 
  InBlocksB b bs = true ->
  wf_block ifs s m f b.
Proof.
  induction bs; intros b Hwfbs Hbinbs.
    inv Hbinbs.

    inv Hwfbs.
    simpl in Hbinbs.
    apply orb_prop in Hbinbs.
    inv Hbinbs; eauto.
      apply blockEqB_inv in H.
      subst. auto.
Qed.

Lemma wf_system__blockInFdefB__wf_block : forall b f ps los nts s ifs,
  blockInFdefB b f = true -> 
  InProductsB (product_fdef f) ps = true ->
  moduleInSystemB (module_intro los nts ps) s = true ->
  wf_system ifs s ->
  wf_block ifs s (module_intro los nts ps) f b.
Proof.
  intros.
  eapply wf_system__wf_fdef in H1; eauto.
  inv H1.  
  eapply wf_blocks__wf_block in H17; eauto.
Qed.

Lemma wf_system__lookup__wf_block : forall b f l0 ps los nts s ifs,
  Some b = lookupBlockViaLabelFromFdef f l0 ->
  InProductsB (product_fdef f) ps = true ->
  moduleInSystemB (module_intro los nts ps) s = true ->
  wf_system ifs s ->
  wf_block ifs s (module_intro los nts ps) f b.
Proof.
  intros.
  eapply wf_system__blockInFdefB__wf_block; eauto.
    symmetry in H. destruct b.
    assert (uniqFdef f) as J. eapply wf_system__uniqFdef; eauto.
    eapply lookupBlockViaLabelFromFdef_inv in H; eauto.
    destruct H; auto.
Qed.

Lemma uniqBlocksLocs__uniqBlockLocs : forall bs b,
  NoDup (getBlocksLocs bs) ->
  InBlocksB b bs = true ->
  NoDup (getBlockLocs b).
Proof.
  induction bs; intros.
     inv H0.

     simpl in *.
     apply orb_prop in H0.
     apply NoDup_inv in H.
     destruct H.
     destruct H0 as [H0 | H0]; subst; auto.
       apply blockEqB_inv in H0; subst; auto.
Qed.

Lemma wf_system__uniq_block : forall b f ps los nts s ifs,
  blockInFdefB b f = true -> 
  InProductsB (product_fdef f) ps = true ->
  moduleInSystemB (module_intro los nts ps) s = true ->
  wf_system ifs s ->
  NoDup (getBlockLocs b).
Proof.
  intros.
  eapply wf_system__uniqFdef in H1; eauto.
  destruct f. destruct f. simpl in *.
  inv H1. inv H3.
  eapply uniqBlocksLocs__uniqBlockLocs; eauto.
Qed.

Lemma wf_cmds__wf_cmd : forall ifs s m f b cs c,
  wf_cmds ifs s m f b cs ->
  In c cs ->
  wf_insn ifs s m f b (insn_cmd c).
Proof.
  induction cs; intros.
    inversion H0.
    
    simpl in H0.
    inv H.
    destruct H0 as [H0 | H0]; subst; eauto.
Qed.

Lemma wf_system__wf_cmd : forall l1 ps1 cs1 tmn1 f ps los nts s ifs c,
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true -> 
  InProductsB (product_fdef f) ps = true ->
  moduleInSystemB (module_intro los nts ps) s = true ->
  wf_system ifs s ->
  In c cs1 ->
  wf_insn ifs s (module_intro los nts ps) f (block_intro l1 ps1 cs1 tmn1) 
    (insn_cmd c).
Proof.
  intros.
  eapply wf_system__blockInFdefB__wf_block in H1; eauto.
  inv H1.
  eapply wf_cmds__wf_cmd; eauto.
Qed.

Lemma wf_system__wf_tmn : forall l1 ps1 cs1 tmn1 f ps los nts s ifs,
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true -> 
  InProductsB (product_fdef f) ps = true ->
  moduleInSystemB (module_intro los nts ps) s = true ->
  wf_system ifs s ->
  wf_insn ifs s (module_intro los nts ps) f (block_intro l1 ps1 cs1 tmn1) 
    (insn_terminator tmn1).
Proof.
  intros.
  eapply wf_system__blockInFdefB__wf_block in H1; eauto.
  inv H1. auto.
Qed.

Lemma wf_tmn__wf_value : forall ifs s m f b tmn v,
  wf_insn ifs s m f b (insn_terminator tmn) ->
  valueInTmnOperands v tmn ->
  exists t, wf_value s m f v t.
Proof.
  intros ifs s m f b tmn v Hwfinsn HvInOps.
  inv Hwfinsn; simpl in HvInOps; subst; try solve [
    eauto | inversion HvInOps
  ].
Qed.

Lemma wf_value__wf_typ : forall s los nts ps f v t,
  wf_value s (module_intro los nts ps) f v t -> 
  wf_typ s t /\ feasible_typ (los, nts) t.
Proof.
  intros.
  inv H; eauto.
Qed.

Lemma entryBlock_has_no_phinodes : forall ifs s f l1 ps1 cs1 tmn1 los nts ps,
  InProductsB (product_fdef f) ps = true ->
  moduleInSystemB (module_intro los nts ps) s = true ->
  wf_system ifs s ->
  getEntryBlock f = Some (block_intro l1 ps1 cs1 tmn1) ->
  ps1 = nil.  
Proof.
  intros ifs s f l1 ps1 cs1 tmn1 los nts ps HFinP HMinS Hwfs Hentry.
  assert (wf_fdef ifs s (module_intro los nts ps) f) as Hwff.
    eapply wf_system__wf_fdef; eauto.
  assert (wf_block ifs s (module_intro los nts ps) f 
    (block_intro l1 ps1 cs1 tmn1)) as Hwfb.
    apply entryBlockInFdef in Hentry.
    eapply wf_system__blockInFdefB__wf_block; eauto.
  inv Hwfb.
  clear H9 H10.
  destruct ps1; auto.
  inv H8.
  clear H9.
  inv H6.
  inv H12.
  unfold check_list_value_l in H5.
  remember (split (unmake_list_value_l value_l_list)) as R.
  destruct R.
  destruct H5 as [J1 [J2 J3]].
  inv Hwff.
  rewrite H14 in Hentry. inv Hentry.
  unfold hasNonePredecessor in H19.
  simpl in *.
  destruct (predOfBlock
            (block_intro l1 (insn_phi id5 typ5 value_l_list :: ps1) cs1 tmn1)
            (genBlockUseDef_blocks blocks5 nil)); inversion H19.
  simpl in J1. contradict J1. omega.
Qed.

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

Lemma wf_phi_operands__elim : forall f b i0 t0 vls0 vid1 l1 n,
  wf_phi_operands f b i0 t0 vls0 ->
  nth_list_value_l n vls0 = Some (value_id vid1, l1) ->
  (vid1 <> i0 \/ (not (isReachableFromEntry f b))) /\
  exists vb, exists b1,
    lookupBlockViaIDFromFdef f vid1 = Some vb /\
    lookupBlockViaLabelFromFdef f l1 = Some b1 /\
    (blockDominates f vb b1 \/ (not (isReachableFromEntry f b))).
Proof.
  induction vls0; intros.
    destruct n; inversion H0.

    destruct v; inv H.
      destruct n; inv H0; eauto.
        split; auto.        
        exists vb. exists b1. split; auto.
      destruct n; inv H0; eauto.
Qed.

Lemma wf_value_list__getValueViaLabelFromValuels__wf_value : forall
  (s : system)
  (m : module)
  (f : fdef)
  (lc : GVMap)
  (l1 : l)
  (t0 : typ)
  v
  l2
  (H2 : wf_value_list
         (make_list_system_module_fdef_value_typ
            (map_list_value_l
               (fun (value_ : value) (_ : l) => (s, m, f, value_, t0)) l2)))
  (J : getValueViaLabelFromValuels l2 l1 = ret v),
  wf_value s m f v t0.
Proof.
  intros.
  induction l2; simpl in *.
    inversion J.
    
    inv H2.
    destruct (l0==l1); subst; eauto.
      inv J. auto.
Qed.        

Lemma wf_value_list__valueInListValue__wf_value : forall s m f v value_list 
  (J : valueInListValue v value_list)
  (H1 : wf_value_list
         (make_list_system_module_fdef_value_typ
            (map_list_value
               (fun value_ : value =>
                (s, m, f, value_, typ_int Size.ThirtyTwo)) value_list))),
  exists t : typ, wf_value s m f v t.
Proof.
  intros.
  unfold valueInListValue in J.
  induction value_list; simpl in *.
    inversion J.
    
    inv H1.
    destruct J as [J | J]; subst; eauto.
Qed.        

Lemma wf_value_list__valueInParams__wf_value : forall s m f v tv_list 
  (H4 : wf_value_list
         (make_list_system_module_fdef_value_typ
            (map_list_typ_value
               (fun (typ_' : typ) (value_'' : value) =>
                (s, m, f, value_'', typ_')) tv_list)))
  (HvInOps : valueInParams v
              (map_list_typ_value
                 (fun (typ_' : typ) (value_'' : value) => (typ_', value_''))
                 tv_list)),
  exists t : typ, wf_value s m f v t.
Proof.
  intros.
  unfold valueInParams in *.
  induction tv_list; simpl in *.
    inversion HvInOps.
    
    inv H4.
    remember (split (map_list_typ_value
                          (fun (typ_' : typ) (value_'' : value) =>
                           (typ_', value_'')) tv_list)) as R.
    destruct R.
    inv HvInOps; eauto.
Qed.        

Lemma wf_value_list__in_params__wf_value : forall S m F tvs
  (H18: wf_value_list
          (make_list_system_module_fdef_value_typ
             (map_list_typ_value
                (fun (typ_' : typ) (value_'' : value) =>
                 (S, m, F, value_'', typ_'))
                tvs)))
  (t1 : typ) (v1 : value),
    In (t1, v1)
     (map_list_typ_value
        (fun (typ_' : typ) (value_'' : value) => (typ_', value_''))
        tvs) ->
    wf_value S m F v1 t1.
Proof.
  induction tvs; simpl; intros.
    inv H.
 
    inv H18. 
    destruct H as [H | H]; eauto.
      inv H; auto.
Qed.

Lemma wf_cmd__wf_value : forall ifs s m f b c v,
  wf_insn ifs s m f b (insn_cmd c) ->
  valueInCmdOperands v c ->
  exists t, wf_value s m f v t.
Proof.
  intros ifs s m f b c v Hwfinsn HvInOps.
  inv Hwfinsn; simpl in HvInOps; subst; try solve [
    eauto |
    destruct HvInOps as [HvInOps | HvInOps]; subst; eauto |
    inv H5; eauto
  ].

    destruct HvInOps as [HvInOps | HvInOps]; subst; eauto.
      eapply wf_value_list__valueInListValue__wf_value; eauto.
     
    destruct HvInOps as [HvInOps | [HvInOps | HvInOps]]; subst; eauto.

    destruct HvInOps as [HvInOps | HvInOps]; subst; eauto.
      eapply wf_value_list__valueInParams__wf_value; eauto.
Qed.

Lemma wf_operand_list__elim : forall ops f1 b1 insn1 id1,
  wf_operand_list ops ->
  In (f1, b1, insn1, id1) (unmake_list_fdef_block_insn_id ops) ->
  wf_operand f1 b1 insn1 id1.
Proof.
  induction ops; intros f1 b1 insn1 id1 Hwfops Hin; simpl in *.
    inversion Hin.

    inv Hwfops.
    destruct Hin as [Hin | Hin]; auto.
      inv Hin; auto.
Qed.     

Lemma wf_insn__wf_insn_base : forall ifs s m f b insn,
  ~ isPhiNode insn -> wf_insn ifs s m f b insn -> wf_insn_base f b insn.
Proof.
  intros ifs s m f b insn Hnonphi Hwf.
  inv Hwf; auto.
    inv H; auto.
    inv H; auto.
    inv H; auto.
    unfold isPhiNode in Hnonphi. simpl in Hnonphi. contradict Hnonphi; auto.
Qed.

(********************************************)
(** * Correctness of analysis *)

Axiom atomset_eq__proof_irr2 : forall (* proof irrelevence *)
  max
  (contents' : ListSet.set atom)
  (inbound' : incl contents' max)
  a
  (Heqdefs' : {|
             DomDS.L.bs_contents := contents';
             DomDS.L.bs_bound := inbound' |} = a),
  contents' = Dominators.bs_contents max a.

Lemma atomset_eq__proof_irr1 : forall
  (bs : blocks)
  (l' : l)
  (t : AMap.t (DomDS.dt (bound_blocks bs)))
  (contents' : ListSet.set atom)
  (inbound' : incl contents' (bound_blocks bs))
  (Heqdefs' : {|
             DomDS.L.bs_contents := contents';
             DomDS.L.bs_bound := inbound' |} = t !! l')
  (bs_contents : ListSet.set atom)
  (bs_bound0 : incl bs_contents (bound_blocks bs))
  (HeqR2 : {|
          DomDS.L.bs_contents := bs_contents;
          DomDS.L.bs_bound := bs_bound0 |} = t !! l'),
  contents' = bs_contents.
Proof. 
  intros.  
  apply atomset_eq__proof_irr2 in Heqdefs'; subst.
  apply atomset_eq__proof_irr2 in HeqR2; subst.
  auto.
Qed.

Lemma reachable_entrypoint:
  forall (f:fdef) l0 ps cs tmn, 
    LLVMlib.getEntryBlock f = Some (block_intro l0 ps cs tmn) ->
    (reachable f)!!l0 = true.
Proof.
  intros f l0 ps cs tmn Hentry. unfold reachable.
  caseEq (reachable_aux f).
    unfold reachable_aux; intros reach A.
    rewrite Hentry in A.
    assert (LBoolean.ge reach!!l0 true).
      eapply ReachDS.fixpoint_entry. eexact A. auto with coqlib.
    unfold LBoolean.ge in H. tauto.

    intros. apply AMap.gi.
Qed.

Lemma reachable_successors:
  forall f l0 cs ps tmn l1,
  uniqFdef f ->
  blockInFdefB (block_intro l0 cs ps tmn) f ->
  In l1 (successors_terminator tmn) ->
  (reachable f)!!l0 = true ->
  (reachable f)!!l1 = true.
Proof.
  intros f l0 cs ps tmn l1 HuniqF HbInF Hin.
  unfold reachable.
  caseEq (reachable_aux f).
    unfold reachable_aux. intro reach; intros.
    remember (LLVMlib.getEntryBlock f) as R.
    destruct R; inv H.
    destruct b as [le ? ? ?].
    assert (LBoolean.ge reach!!l1 reach!!l0) as J.
      change (reach!!l0) with ((fun pc r => r) l0 (reach!!l0)).
      eapply ReachDS.fixpoint_solution; eauto.
        destruct f as [[?] bs]. simpl in *.
        clear - HuniqF HbInF Hin. destruct HuniqF.
        assert ((successors_terminator tmn) = (successors_blocks bs) !!! l0) 
          as EQ.
          eapply successors_terminator__successors_blocks; eauto.
        rewrite <- EQ; auto.            
    elim J; intro. congruence. auto.

  intros. apply AMap.gi.
Qed.

Lemma dom_successors : forall
  (bs : blocks)
  (l3 : l)
  (l' : l)
  ps cs tmn fh ifs s m
  (HwfF : wf_fdef ifs s m (fdef_intro fh bs))
  (Huniq : uniqBlocks bs)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) (fdef_intro fh bs) = true)
  (Doms : AMap.t
           (Dominators.t (bound_fdef (fdef_intro fh bs))))
  (HeqDoms : Doms = dom_analyze (fdef_intro fh bs))
  (contents3 : ListSet.set atom)
  (inbound3 : incl contents3 (bound_fdef (fdef_intro fh bs)))
  (Heqdefs3 : {|
             DomDS.L.bs_contents := contents3;
             DomDS.L.bs_bound := inbound3 |} = Doms !! l3)
  (Hsucc : In l' (successors_terminator tmn))
  (contents' : ListSet.set atom)
  (inbound' : incl contents' (bound_fdef (fdef_intro fh bs)))
  (Heqdefs' : {|
             DomDS.L.bs_contents := contents';
             DomDS.L.bs_bound := inbound' |} = Doms !! l'),
  incl contents' (l3 :: contents3).
Proof. 
  intros. simpl in *.
  unfold dom_analyze in *.
  remember (entry_dom bs) as R.
  destruct R as [R Hp].
  destruct R as [[le start] | ].
  Case "entry is good".
    remember (DomDS.fixpoint (bound_blocks bs) (successors_blocks bs)
                (transfer (bound_blocks bs)) ((le, start) :: nil)) as R1.
    destruct start.
    destruct bs_contents; tinv Hp.
    destruct bs_contents; tinv Hp.
    destruct R1; subst.
    SCase "analysis is done".
      symmetry in HeqR1.
      assert (In l' (successors_blocks bs) !!! l3) as J1.
        clear - HBinF Hsucc Huniq.
        assert (successors_terminator tmn = (successors_blocks bs) !!! l3) as EQ.
          eapply successors_terminator__successors_blocks; eauto.
        rewrite <- EQ. auto.
      
      apply DomDS.fixpoint_solution with (s:=l')(n:=l3) in HeqR1; eauto.
      unfold transfer, DomDS.L.ge, DomDS.L.top, DomDS.L.bot, DomDS.L.sub, 
        DomDS.L.eq, Dominators.add in HeqR1.
      remember (t !! l') as R2.
      destruct R2.              
      assert (contents' = bs_contents) as EQ.
        clear - Heqdefs' HeqR2.
        eapply atomset_eq__proof_irr1; eauto.
      subst.
      remember (t !! l3) as R3.
      destruct R3.              
      assert (contents3 = bs_contents0) as EQ.
        clear - Heqdefs3 HeqR3.
        eapply atomset_eq__proof_irr1; eauto.
      subst.
      clear - Heqdefs3 Heqdefs' HeqR2 HeqR3 HeqR1.
      destruct HeqR1 as [HeqR1 | [HeqR1 | HeqR1]].
        destruct HeqR1 as [G1 G2].
        intros x G.
        apply G1 in G. inversion G.
        destruct (in_dec eq_atom_dec l3 (bound_blocks bs)).
          eapply incl_set_eq_right; eauto using set_eq_sym.
          apply incl_tran with (m:=bs_contents0).
            eapply incl_set_eq_right; eauto using set_eq_sym.
            apply incl_tl; auto using incl_refl.
          
        destruct (in_dec eq_atom_dec l3 (bound_blocks bs)); auto.
          apply incl_tl; auto.

    SCase "analysis fails".
      subst.
      unfold Dominators.top in Heqdefs3, Heqdefs'.
      simpl in Heqdefs3, Heqdefs'.
      assert (exists ps, exists cs, exists tmn,
        getEntryBlock (fdef_intro fh bs) = Some (block_intro a ps cs tmn)).
        unfold entry_dom in HeqR.
        destruct bs.
          inversion HeqR.
          destruct b. inv HeqR.
          exists p. exists c. exists t. auto.
      assert (l' <> a) as Neq.
        clear - H Hsucc HwfF HBinF. 
        destruct H as [ps1 [cs1 [tmn1 H]]].
        eapply getEntryBlock_inv; eauto.
      rewrite AMap.gso in Heqdefs'; auto.
      rewrite AMap.gi in Heqdefs'.
      inv Heqdefs'.
      clear.
      intros x J. inversion J.

  Case "entry is wrong".   
    subst. inversion HBinF.
Qed.

Lemma dom_entrypoint : forall f l0 ps cs tmn
  (Hentry : LLVMlib.getEntryBlock f = Some (block_intro l0 ps cs tmn)),
  incl (Dominators.bs_contents (bound_fdef f) ((dom_analyze f) !! l0)) [l0].
Proof.
  intros.
  unfold dom_analyze.
  destruct f.
  remember (entry_dom b) as R.
  destruct R as [R Hp].
  destruct R as [[le start] | ].
  Case "entry is good". 
    remember (DomDS.fixpoint (bound_blocks b) (successors_blocks b)
                (transfer (bound_blocks b)) ((le, start) :: nil)) as R1.
    destruct start.
    destruct bs_contents; tinv Hp.
    destruct bs_contents; tinv Hp.
    subst le. 
    destruct b; try solve [inversion HeqR].
    destruct b. simpl in HeqR. inversion HeqR. subst a.
    simpl in Hentry. inversion Hentry. subst l0 p c t.
    clear HeqR Hentry.    
    destruct R1; subst.
    SCase "analysis is done".
      symmetry in HeqR1.
      apply DomDS.fixpoint_entry with (n:=l1)(v:={|
                DomDS.L.bs_contents := l1 :: nil;
                DomDS.L.bs_bound := bs_bound |}) in HeqR1; simpl; eauto.
      unfold DomDS.L.ge in HeqR1.
      unfold DomDS.L.eq, DomDS.L.top, DomDS.L.bot, DomDS.L.sub in HeqR1.
      simpl in *.

      remember (t !! l1) as R.
      destruct R.
      erewrite <- atomset_eq__proof_irr2; eauto.
      destruct HeqR1 as [HeqR1 | [ HeqR1 | HeqR1 ]]; auto.
      SSCase "1".       
        apply set_eq_empty_inv in HeqR1. subst.
        intros x J. inversion J.
      SSCase "2".   
        eapply incl_set_eq_right; eauto using set_eq_sym.
    
    SCase "analysis fails".
      simpl.      
      rewrite AMap.gss. simpl.
      apply incl_refl.

  Case "entry is wrong". 
    subst. inversion Hentry.
Qed.

(***************************)
(* domination prop *)

Fixpoint cmds_dominates_cmd (cs:cmds) (id0:id) : list atom :=
match cs with
| nil => nil
| c1::cs' => 
    let ctx := cmds_dominates_cmd cs' id0 in
    if eq_atom_dec (getCmdLoc c1) id0 then nil
    else
      match getCmdID c1 with
      | Some id1 => id1::ctx
      | None => ctx
      end
end.

Lemma NoDup__In_cmds_dominates_cmd : forall cs1 c cs2 id1,
  NoDup (getCmdsLocs (cs1 ++ c :: cs2)) ->
  In id1 (getCmdsIDs cs1) ->
  In id1 (cmds_dominates_cmd (cs1 ++ c :: cs2) (getCmdLoc c)).
Proof.
  induction cs1; intros; simpl in *.
    inversion H0.

    inv H.
    destruct (eq_atom_dec (getCmdLoc a) (getCmdLoc c)).
      assert (False) as F.
        apply H3. 
        rewrite e.
        rewrite getCmdsLocs_app. simpl.
        apply in_or_app. right. simpl. auto.
      inversion F.

      destruct (getCmdID a); auto.
      simpl in *. destruct H0 as [H0 | H0]; auto.
Qed.   

Definition inscope_of_block (f:fdef) (l1:l) (opt_ctx:option (list atom)) (lbl:l)
  :=
  match opt_ctx with
  | Some ctx =>
     match lookupBlockViaLabelFromFdef f lbl with
     | None => None
     | Some b => 
         if eq_atom_dec lbl l1 then Some ctx
         else Some (getBlockIDs b ++ ctx)
     end
  | None => None
  end.

Definition inscope_of_cmd (f:fdef) (b1:block) (c:cmd) : option (list atom) :=
let id0 := getCmdLoc c in
let '(block_intro l1 ps cs _) := b1 in
let '(fdef_intro (fheader_intro _ _ _ la _) _) := f in
let 'dt := dom_analyze f in
let '(Dominators.mkBoundedSet els _) := AMap.get l1 dt in
fold_left (inscope_of_block f l1) els
  (Some (getPhiNodesIDs ps ++ cmds_dominates_cmd cs id0 ++ getArgsIDs la))
.

Definition inscope_of_tmn (f:fdef) (b1:block) (tmn:terminator) 
  : option (list atom) :=
let '(block_intro l1 ps cs _) := b1 in
let '(fdef_intro (fheader_intro _ _ _ la _) _) := f in
let 'dt := dom_analyze f in
let '(Dominators.mkBoundedSet els _) := AMap.get l1 dt in
fold_left (inscope_of_block f l1) els
  (Some (getPhiNodesIDs ps ++ getCmdsIDs cs ++ getArgsIDs la))
.

Definition defs_dominate (f:fdef) (curb incomingb:block) (i:insn) 
  : option (list atom) :=
match i with
| insn_phinode p => 
    let '(block_intro _ _ _ tmn) := incomingb in
    inscope_of_tmn f incomingb tmn
| insn_cmd c => inscope_of_cmd f curb c
| insn_terminator tmn => inscope_of_tmn f curb tmn
end.

Lemma getCmdsIDs__cmds_dominates_cmd : forall cs2' c',
  ~ In (getCmdLoc c') (LLVMlib.getCmdsLocs cs2') ->
  set_eq _ (getCmdsIDs (cs2' ++ [c']))
  (cmds_dominates_cmd (cs2' ++ [c']) (getCmdLoc c') ++ 
    match getCmdID c' with
    | Some id1 => [id1]
    | None => nil
    end).   
Proof.
  induction cs2'; intros c' Hnotin.
    simpl in *.
    destruct (eq_atom_dec (getCmdLoc c') (getCmdLoc c')) as [_ | n];
      try solve [contradict n; auto].
      remember (getCmdID c') as R.
      destruct R; simpl_env; apply set_eq_refl.

    simpl in *.
    assert (~ In (getCmdLoc c') (getCmdsLocs cs2')) as J.
      auto.
    apply IHcs2' in J.
    remember (getCmdID a) as R1.
    remember (getCmdID c') as R2.
    destruct (eq_atom_dec (getCmdLoc a) (getCmdLoc c')); 
      try solve [contradict e; auto].
    destruct R1; auto.
      simpl_env.
      apply set_eq_app; auto using set_eq_refl.
Qed.      

Definition opt_set_eq (ops1 ops2:option (list atom)) : Prop :=
match (ops1, ops2) with
| (None, None) => True
| (Some s1, Some s2) => set_eq _ s1 s2
| _ => False
end.

Lemma inscope_of_block__opt_set_eq : forall f l1 l' opr1 opr2,
  opt_set_eq opr1 opr2 ->
  opt_set_eq (inscope_of_block f l1 opr1 l') (inscope_of_block f l1 opr2 l').
Proof.
  unfold inscope_of_block.
  intros.
  destruct (lookupBlockViaLabelFromFdef f l').
    destruct (eq_atom_dec l' l1); subst.
      destruct opr1.
        destruct opr2; try solve [inversion H | auto].
        destruct opr2; try solve [inversion H | auto].
      unfold opt_set_eq in *.
      destruct opr1.
        destruct opr2; try solve [inversion H ].
          apply set_eq_app; auto using set_eq_refl.
        destruct opr2; try solve [inversion H | auto ].
    unfold opt_set_eq in *.
    destruct opr1.
      destruct opr2; try solve [inversion H | auto].
      destruct opr2; try solve [inversion H | auto].
Qed.
 
Lemma fold_left__opt_set_eq_aux : forall ls0 opr1 opr2 f l1,
  opt_set_eq opr1 opr2 ->
  opt_set_eq (fold_left (inscope_of_block f l1) ls0 opr1) 
           (fold_left (inscope_of_block f l1) ls0 opr2).
Proof.
  induction ls0; intros opr1 opr2 f l1 Heq; simpl in *; auto.
    apply IHls0.
      apply inscope_of_block__opt_set_eq; auto.
Qed.

Lemma fold_left__opt_set_eq : forall (ls0:list atom) f l1 init1 init2 r1,
  set_eq _ init1 init2 ->  
  fold_left (inscope_of_block f l1) ls0 (Some init1) = Some r1 ->
  exists r2, fold_left (inscope_of_block f l1) ls0 (Some init2) = Some r2 /\ 
    set_eq _ r1 r2.
Proof.
  intros.
  assert (opt_set_eq (Some init1) (Some init2)) as EQ. unfold opt_set_eq. auto.
  apply fold_left__opt_set_eq_aux with (ls0:=ls0)(f:=f)(l1:=l1) in EQ.
  remember (fold_left (inscope_of_block f l1) ls0 (ret init2)) as R. 
  unfold opt_set_eq in EQ.    
  rewrite H0 in EQ.
  destruct R; try solve [inversion EQ].
  exists l0. auto.
Qed.
 
Lemma inscope_of_block__opt_union : forall f l1 l' init1 init2 r1,
  inscope_of_block f l1 (Some init1) l' = Some r1 ->
  exists r2, inscope_of_block f l1 (Some (init1++init2)) l' = Some r2 /\
    set_eq _ (r1++init2) r2.
Proof.
  intros.
  unfold inscope_of_block in *.
  destruct (lookupBlockViaLabelFromFdef f l').
    destruct (eq_atom_dec l' l1); subst; inv H.
      exists (r1++init2). auto using set_eq_refl.
      exists (getBlockIDs b ++ init1 ++ init2). 
        simpl_env. auto using set_eq_refl.
    inversion H.
Qed.

Lemma fold_left__none : forall (ls0:list atom) f l1,
  fold_left (inscope_of_block f l1) ls0 None = None.
Proof.
  induction ls0; intros f l1; simpl in *; auto.
Qed.

Lemma fold_left__opt_union : forall (ls0:list atom) f l1 init1 init2 r1,
  fold_left (inscope_of_block f l1) ls0 (Some init1) = Some r1 ->
  exists r2, 
    fold_left (inscope_of_block f l1) ls0 (Some (init1++init2)) = Some r2 
      /\ set_eq _ (r1++init2) r2.
Proof.
  induction ls0; intros f l1 init1 init2 r1 H; simpl in *; auto.
    inv H. exists (r1 ++ init2). split; auto using set_eq_refl.

    destruct (lookupBlockViaLabelFromFdef f a).
      destruct (eq_atom_dec a l1); subst; auto.
        apply IHls0 with (init2:=init2) in H; auto.
          simpl_env in H. auto.
      rewrite fold_left__none in H. inversion H.
Qed.

Lemma inscope_of_cmd_tmn : forall f l2 ps2 cs2' c' tmn' ids1,
~ In (getCmdLoc c') (getCmdsLocs cs2') ->
Some ids1 = inscope_of_cmd f (block_intro l2 ps2 (cs2'++[c']) tmn') c' ->
exists ids2, 
  Some ids2 = inscope_of_tmn f (block_intro l2 ps2 (cs2'++[c']) tmn') tmn' /\
  match getCmdID c' with
  | Some id1 => set_eq _ (id1::ids1) ids2
  | None => set_eq _ ids1 ids2
  end.
Proof.
  intros f l2 ps2 cs2' c' tmn' ids1 Hnotin Hinscope.
  unfold inscope_of_cmd in Hinscope.
  unfold inscope_of_tmn.
  destruct f as [[? ? ? la va] bs].
  remember ((dom_analyze (fdef_intro (fheader_intro f t i0 la va) bs)) !! l2) as R.
  destruct R as [R_contents R_bound]. simpl in *.
  apply getCmdsIDs__cmds_dominates_cmd in Hnotin.
  symmetry in Hinscope.
  remember (getCmdID c') as R.
  destruct R.
    apply fold_left__opt_union with (init2:=[i1]) in Hinscope.
    destruct Hinscope as [r2 [Hinscope Heq]].
    apply fold_left__opt_set_eq with (init2:=((getPhiNodesIDs ps2) ++
      ((getCmdsIDs (cs2' ++ [c'])) ++ (getArgsIDs la)))) in Hinscope.
      destruct Hinscope as [r3 [Hinscope Heq']].
      exists r3.     
      split; auto.
        simpl_env. 
        eapply set_eq_trans with (y:=r2); eauto.
        eapply set_eq_trans with (y:=ids1 ++ [i1]); eauto.
          apply set_eq_swap.          
      simpl_env.
      apply set_eq_app; auto using set_eq_refl.
      apply set_eq_trans with (y:=(cmds_dominates_cmd (cs2' ++ [c']) 
         (getCmdLoc c') ++ [i1]) ++ getArgsIDs la).
        simpl_env.
        apply set_eq_app; auto using set_eq_refl.
          apply set_eq_swap.          

        apply set_eq_app; auto using set_eq_refl.
          apply set_eq_sym; auto.          

    apply fold_left__opt_set_eq with (init2:=((getPhiNodesIDs ps2) ++ 
      ((getCmdsIDs (cs2' ++ [c'])) ++ (getArgsIDs la)))) in Hinscope.
      destruct Hinscope as [r3 [Hinscope Heq']].
      exists r3.     
      split; auto.
      apply set_eq_app; auto using set_eq_refl.
      apply set_eq_app; auto using set_eq_refl.
      simpl_env in Hnotin.
      apply set_eq_sym; auto.          
Qed.

Lemma cmds_dominates_cmd__cmds_dominates_cmd : forall cs2' c' c cs',
  NoDup (getCmdsLocs (cs2'++[c']++[c]++cs')) ->
  set_eq _ (cmds_dominates_cmd (cs2' ++ c' :: c :: cs') (getCmdLoc c))
    (cmds_dominates_cmd (cs2' ++ c' :: c :: cs') (getCmdLoc c') ++
     match getCmdID c' with
     | Some id1 => [id1]
     | None => nil
     end).   
Proof.
  induction cs2'; intros c' c cs' Hnodup.
    simpl in *.
    inv Hnodup. simpl in H1.
    remember (getCmdID c') as R.
    destruct (eq_atom_dec (getCmdLoc c') (getCmdLoc c)).
      contradict e; auto.

      destruct (eq_atom_dec (getCmdLoc c) (getCmdLoc c)) as [_|n1];
        try solve [contradict n1; auto].
      destruct (eq_atom_dec (getCmdLoc c') (getCmdLoc c')) as [_|n2];
        try solve [contradict n2; auto].
      destruct R; auto using set_eq_refl.

    simpl in *.
    inv Hnodup.
    rewrite getCmdsLocs_app in H1.
    apply NotIn_inv in H1.    
    destruct H1 as [H11 H12].
    simpl in H12.
    destruct (eq_atom_dec (getCmdLoc a) (getCmdLoc c)) as [e1 | ];
      try solve [contradict e1; auto].
    destruct (eq_atom_dec (getCmdLoc a) (getCmdLoc c')) as [e1 | ];
      try solve [contradict e1; auto].
    destruct (getCmdID a); auto.
      apply IHcs2' in H2. clear IHcs2'.
      simpl_env.
       apply set_eq_app; auto using set_eq_refl.
Qed.      

Lemma inscope_of_cmd_cmd : forall f l2 ps2 cs2' c' c cs' tmn' ids1,
NoDup (getCmdsLocs (cs2'++[c']++[c]++cs')) ->
Some ids1 = inscope_of_cmd f (block_intro l2 ps2 (cs2'++[c']++[c]++cs') tmn') c' 
  ->
exists ids2, 
  Some ids2 = 
    inscope_of_cmd f (block_intro l2 ps2 (cs2'++[c']++[c]++cs') tmn') c /\
  match getCmdID c' with
  | Some id1 => set_eq _ (id1::ids1) ids2
  | None => set_eq _ ids1 ids2
  end.
Proof.
  intros f l2 ps2 cs2' c' c cs' tmn' ids1 Hnodup Hinscope.
  unfold inscope_of_cmd in Hinscope.
  unfold inscope_of_cmd.
  destruct f as [[? ? ? la va] bs].
  remember ((dom_analyze (fdef_intro (fheader_intro f t i0 la va) bs)) !! l2) as R.
  destruct R as [R_contents R_bound].
  apply cmds_dominates_cmd__cmds_dominates_cmd in Hnodup. simpl in *.
  symmetry in Hinscope.
  remember (getCmdID c') as R.
  destruct R.
    apply fold_left__opt_union with (init2:=[i1]) in Hinscope.
    destruct Hinscope as [r2 [Hinscope Heq]].
    apply fold_left__opt_set_eq with (init2:=((getPhiNodesIDs ps2) ++ 
      ((cmds_dominates_cmd (cs2' ++ c' :: c :: cs') (getCmdLoc c)) ++
      (getArgsIDs la)))) in Hinscope.
      destruct Hinscope as [r3 [Hinscope Heq']].
      exists r3.     
      split; auto.
        simpl_env. 
        eapply set_eq_trans with (y:=r2); eauto.
        eapply set_eq_trans with (y:=ids1 ++ [i1]); eauto.
          apply set_eq_swap.          
      simpl_env.
      apply set_eq_app; auto using set_eq_refl.
      apply set_eq_trans with (y:=(cmds_dominates_cmd (cs2' ++ [c']++[c]++cs') 
         (getCmdLoc c') ++ [i1]) ++ getArgsIDs la).
        simpl_env.
        apply set_eq_app; auto using set_eq_refl.
          apply set_eq_swap.          

        apply set_eq_app; auto using set_eq_refl.
          apply set_eq_sym; auto.          

    apply fold_left__opt_set_eq with (init2:=((getPhiNodesIDs ps2) ++
      ((cmds_dominates_cmd (cs2' ++ c' :: c :: cs') (getCmdLoc c)) ++
      (getArgsIDs la)))) in Hinscope.
      destruct Hinscope as [r3 [Hinscope Heq']].
      exists r3.     
      split; auto.
      apply set_eq_app; auto using set_eq_refl.
      apply set_eq_app; auto using set_eq_refl.
      simpl_env in Hnodup.
      apply set_eq_sym; auto.          
Qed.

Lemma fold_left__bound_blocks : forall ls0 fa t i0 la va bs l0 init,
  incl ls0 (bound_blocks bs) ->
  exists r, 
    fold_left (inscope_of_block 
      (fdef_intro (fheader_intro fa t i0 la va) bs) l0) ls0 (Some init) = 
       Some r.
Proof.
  induction ls0; intros fa t i0 la va bs l0 init Hinc; simpl in *.
    exists init. auto.

    assert (incl ls0 (bound_blocks bs)) as J.
      simpl_env in Hinc.
      eapply incl_app_invr; eauto.
    assert (exists b, lookupAL block (genLabel2Block_blocks bs) a = Some b) 
      as Hlkup.
      clear - Hinc.
      simpl_env in Hinc.
      apply incl_app_invl in Hinc.
      apply inc__getLabel2Block_blocks; auto.

    destruct Hlkup as [b Hlkup].
    rewrite Hlkup. 
    destruct (eq_atom_dec a l0); subst; auto.
Qed.

Lemma fold_left__spec : forall ls0 l0 init r f,
  fold_left (inscope_of_block f l0) ls0 (Some init) = Some r ->
    incl init r /\
    (forall l1 b1, 
      In l1 (ListSet.set_diff eq_atom_dec ls0 [l0]) -> 
      lookupBlockViaLabelFromFdef f l1 = Some b1 ->
      incl (getBlockIDs b1) r) /\
    (forall id1,
      In id1 r ->
      In id1 init \/
      exists b1, exists l1, In l1 (ListSet.set_diff eq_atom_dec ls0 [l0]) /\
        lookupBlockViaLabelFromFdef f l1 = Some b1 /\
        In id1 (getBlockIDs b1)
    ).
Proof.
  induction ls0; intros l0 init r f Hfold; simpl in *.
    inv Hfold.
    split. apply incl_refl.
    split; auto. 
      intros ? ? Hfalse. inversion Hfalse.
      
    remember (lookupBlockViaLabelFromFdef f a) as R.
    destruct R.
      destruct (eq_atom_dec a l0); subst; auto.
      apply IHls0 in Hfold.
      destruct Hfold as [J1 [J2 J3]].
      split.
        eapply incl_app_invr; eauto.
      split.
        intros l1 b1 Hin Hlkup.
        apply ListSet.set_add_elim in Hin.
        destruct Hin as [Hin | Hin]; subst; eauto.                  
          rewrite Hlkup in HeqR. inv HeqR.
          eapply incl_app_invl; eauto.
        intros id1 Hin.
        apply J3 in Hin.
        destruct Hin as [Hin | [b1 [l1 [H1 [H2 H3]]]]].
          apply in_app_or in Hin.
          destruct Hin as [Hin | Hin]; auto.
          right. 
          exists b. exists a.
          split; auto.
            apply ListSet.set_add_intro; auto.
             
          right.
          exists b1. exists l1.
          split; auto.
            apply ListSet.set_add_intro; auto.

      rewrite fold_left__none in Hfold. inversion Hfold.
Qed.

Lemma wf_value_list__getValueViaBlockFromValuels__wf_value : forall
  (s : system)  (m : module)  (f : fdef)  (lc : GVMap) b (t0 : typ) v l2
  (H2 : wf_value_list
         (make_list_system_module_fdef_value_typ
            (map_list_value_l
               (fun (value_ : value) (_ : l) => (s, m, f, value_, t0)) l2)))
  (J : getValueViaBlockFromValuels l2 b = ret v),
  wf_value s m f v t0.
Proof.
  intros. destruct b. simpl in J.
  eapply wf_value_list__getValueViaLabelFromValuels__wf_value in H2; eauto.
Qed.        
   
Lemma NoDup_lookupTypViaIDFromPhiNodes : forall ps1 i0 t0 l0 ps2,
  NoDup (getPhiNodesIDs (ps1 ++ insn_phi i0 t0 l0 :: ps2)) ->
  lookupTypViaIDFromPhiNodes (ps1 ++ insn_phi i0 t0 l0 :: ps2) i0 = Some t0.
Proof.
  induction ps1; simpl; unfold lookupTypViaIDFromPhiNode; simpl; intros.
    destruct (i0 == i0); auto.
      contradict n; auto.

    destruct a.
    inv H. simpl.
    destruct (i0 == i1); subst; auto.
      rewrite getPhiNodesIDs_app in H2. simpl in H2.
      contradict H2.
      apply in_or_app. simpl. auto.
Qed.

Lemma wf_fdef__wf_phinodes : forall ifs s m f l3 cs tmn ps,
  wf_fdef ifs s m f ->
  blockInFdefB (block_intro l3 ps cs tmn) f ->
  wf_phinodes ifs s m f (block_intro l3 ps cs tmn) ps.
Proof.
  intros.
  inv H.
  eapply wf_blocks__wf_block in H9; eauto.
  inv H9; auto.
Qed.

Lemma wf_typ_list__in_args__wf_typ : forall s typ_attributes_id_list
  (H18: wf_typ_list
          (make_list_system_typ
             (map_list_typ_attributes_id
                (fun (typ_ : typ) (_ : attributes) (_ : id) => (s, typ_))
                typ_attributes_id_list)))
  t a i0,
    In (t, a, i0)
       (map_list_typ_attributes_id
         (fun (typ_ : typ) (attributes_ : attributes) (id_ : id) =>
          (typ_, attributes_, id_)) typ_attributes_id_list) ->
    wf_typ s t.
Proof.
  induction typ_attributes_id_list; simpl; intros.
    inv H.
 
    inv H18. 
    destruct H as [H | H]; eauto.
      inv H; auto.
Qed.

Lemma feasible_typ_list__in_args__feasible_typ : forall los nts 
  typ_attributes_id_list
  (H18: feasible_typ_targetdata_paren_targetdata_def_list
          (make_list_layouts_namedts_typ
             (map_list_typ_attributes_id
                (fun (typ_ : typ) (_ : attributes) (_ : id) =>
                 (los, nts, typ_)) typ_attributes_id_list)))
  t a i0,
    In (t, a, i0)
       (map_list_typ_attributes_id
         (fun (typ_ : typ) (attributes_ : attributes) (id_ : id) =>
          (typ_, attributes_, id_)) typ_attributes_id_list) ->
    feasible_typ (los,nts) t.
Proof.
  induction typ_attributes_id_list; simpl; intros.
    inv H.
 
    inv H18. 
    destruct H as [H | H]; eauto.
      inv H; auto.
Qed.

Lemma gundef_p1__total : forall TD, exists mp', gundef TD (typ_pointer (typ_int 1%nat)) = ret mp'.
Proof.
  intros. unfold gundef. destruct TD. simpl. eauto.
Qed.

Lemma gundef_i1__total : forall TD, exists mp', gundef TD (typ_int 1%nat) = ret mp'.
Proof.
  intros. unfold gundef. destruct TD. simpl. eauto.
Qed.

Lemma in_middle : forall A (c:A) cs1 cs2, In c (cs1 ++ c :: cs2).
Proof.
  intros.
  apply in_app_iff; simpl; auto.
Qed.

Lemma mgetoffset_aux__getSubTypFromConstIdxs : forall TD const_list idxs o t' 
    t1 o0
  (HeqR1 : ret idxs = intConsts2Nats TD const_list)
  (HeqR2 : ret (o, t') = mgetoffset_aux TD t1 idxs o0),
  getSubTypFromConstIdxs const_list t1 = ret t'.
Proof.
  induction const_list; simpl; intros.
    inv HeqR1. simpl in HeqR2. inv HeqR2. auto.

    destruct c; tinv HeqR1.
    destruct (Size.dec s Size.ThirtyTwo); tinv HeqR1.
    remember (intConsts2Nats TD const_list) as R3.
    destruct R3; inv HeqR1.
    destruct t1; tinv HeqR2.
      simpl in HeqR2.
      destruct (getTypeAllocSize TD t1); inv HeqR2; eauto.
      simpl in HeqR2.
      destruct (_getStructElementOffset TD l1 (Coqlib.nat_of_Z 
        (INTEGER.to_Z i0)) 0); inv HeqR2; eauto.
      unfold INTEGER.to_Z in H0. unfold INTEGER.to_nat.
      destruct (nth_list_typ (Coqlib.nat_of_Z i0) l1); tinv H0.
      simpl in H0. eauto.
Qed.

Lemma mgetoffset__getSubTypFromConstIdxs : forall TD const_list idxs o t' t1
  (HeqR1 : ret idxs = intConsts2Nats TD const_list)
  (HeqR2 : ret (o, t') = mgetoffset TD t1 idxs),
  getSubTypFromConstIdxs const_list t1 = ret t'.
Proof.
  unfold mgetoffset. intros.
  eapply mgetoffset_aux__getSubTypFromConstIdxs; eauto.
Qed.

Definition wf_zeroconst2GV_total_prop (t:typ) := forall TD,
  Constant.wf_zeroconst_typ t -> Constant.feasible_typ TD t ->
  exists gv, zeroconst2GV TD t = Some gv.

Definition wf_zeroconsts2GV_total_prop (lt:list_typ) := forall TD,
  Constant.wf_zeroconsts_typ lt -> Constant.feasible_typs TD lt ->
  exists gvn, zeroconsts2GV TD lt = Some gvn.

Lemma feasible_typ_inv'' : forall TD t,
  Constant.feasible_typ TD t -> 
  exists ssz, exists asz, 
    getTypeStoreSize TD t = Some ssz /\ getTypeAllocSize TD t = Some asz.
Proof.
  intros TD t Hs.
  apply feasible_typ_inv' in Hs.
  destruct Hs as [sz [al [J1 J2]]].
  unfold getTypeAllocSize, getTypeStoreSize, getTypeSizeInBits, 
    getABITypeAlignment, getAlignment.
  rewrite J1. eauto.
Qed.

Lemma wf_zeroconst2GV_total_mutrec :
  (forall t, wf_zeroconst2GV_total_prop t) *
  (forall lt, wf_zeroconsts2GV_total_prop lt).
Proof.
  apply typ_mutrec; 
    unfold wf_zeroconst2GV_total_prop, wf_zeroconsts2GV_total_prop;
    intros; simpl in *; try solve [eauto | inversion H | inversion H1 ].
Case "float".
  destruct f; try solve [eauto | inversion H].
Case "array".
  destruct H with (TD:=TD) as [gv Hz2c]; auto.
  rewrite Hz2c.
  destruct s; eauto.
  apply feasible_typ_inv'' in H1. 
  destruct H1 as [ssz [asz [J1 J2]]].
  rewrite J2.
  eauto.

Case "struct".
  destruct (@H TD) as [gv Hz2c]; auto.
  rewrite Hz2c. destruct gv; eauto.

Case "cons".
  destruct H1 as [J1 J2].
  destruct H2 as [J3 J4].
  destruct (@H TD) as [gv Hz2c]; auto.
  destruct (@H0 TD) as [gvs Hz2cs]; auto.
  rewrite Hz2cs. rewrite Hz2c.
  apply feasible_typ_inv'' in J3.  
  destruct J3 as [ssz [asz [J6 J5]]].
  rewrite J5. eauto.
Qed.

Lemma wf_zeroconst2GV_total : forall TD t,
  Constant.wf_zeroconst_typ t ->
  Constant.feasible_typ TD t ->
  exists gv, zeroconst2GV TD t = Some gv.
Proof.
  intros.
  destruct wf_zeroconst2GV_total_mutrec as [J _].
  apply J; auto.
Qed.

Lemma gundef__total : forall TD t
  (H0 : Constant.feasible_typ TD t),
  exists gv, gundef TD t = Some gv.
Proof.
  intros. 
  unfold gundef.
  eapply feasible_typ_inv' in H0; eauto.
  destruct H0 as [sz [al [J1 J2]]].
  unfold getTypeSizeInBits.
  rewrite J1. eauto.
Qed.

Lemma gundef__total' : forall TD t
  (H0 : feasible_typ TD t),
  exists gv, gundef TD t = Some gv.
Proof.
  intros. inv H0. apply gundef__total; auto.
Qed.

Lemma fit_gv__total : forall TD t gv1
  (H0 : Constant.feasible_typ TD t),
  exists gv, fit_gv TD t gv1 = Some gv.
Proof.
  intros.
  unfold fit_gv.
  assert (exists gv, gundef TD t = Some gv) as EQ.
    apply gundef__total; auto.
  destruct EQ as [gv EQ].
  rewrite EQ.
  eapply feasible_typ_inv' in H0; eauto.
  destruct H0 as [sz [al [J1 J2]]].
  unfold getTypeSizeInBits.
  rewrite J1. 
  destruct (sizeGenericValue gv1 =n= nat_of_Z (ZRdiv (Z_of_nat sz) 8)); eauto.
Qed.

Lemma wf_trunc__wf_typ : forall ifs s los nts ps f b i0 t t0 v t1,
  wf_trunc ifs s (module_intro los nts ps) f b 
    (insn_cmd (insn_trunc i0 t t0 v t1)) ->
  wf_typ s t1 /\ feasible_typ (los, nts) t1.
Proof.
  intros.
  inv H; auto.
Qed.

Lemma lookupBlockViaLabelFromFdef_prop : forall l1 p c t f l3 
  (Huniq: uniqFdef f),
  ret block_intro l1 p c t = lookupBlockViaLabelFromFdef f l3 ->
  ret block_intro l1 p c t = lookupBlockViaLabelFromFdef f l1.
Proof.
  intros.
  assert (J:=H).
  symmetry in H.
  eapply lookupBlockViaLabelFromFdef_inv in H; eauto.
  destruct H; subst. auto.
Qed.

Lemma wf_trunc__wf_value : forall ifs s los nts ps f b i0 t t0 v t1,
  wf_trunc ifs s (module_intro los nts ps) f b 
    (insn_cmd (insn_trunc i0 t t0 v t1)) ->
  wf_value s (module_intro los nts ps) f v t0.
Proof.
  intros.
  inv H; auto.
Qed.

Lemma wf_ext__wf_typ : forall ifs s los nts ps f b i0 e t0 v t1,
  wf_ext ifs s (module_intro los nts ps) f b 
    (insn_cmd (insn_ext i0 e t0 v t1)) ->
  wf_typ s t1 /\ feasible_typ (los, nts) t1.
Proof.
  intros.
  inv H; auto.
Qed.

Lemma wf_ext__wf_value : forall ifs s los nts ps f b i0 e t0 v t1,
  wf_ext ifs s (module_intro los nts ps) f b 
    (insn_cmd (insn_ext i0 e t0 v t1)) ->
  wf_value s (module_intro los nts ps) f v t0.
Proof.
  intros.
  inv H; auto.
Qed.

(************** GenericValue ******************)

Scheme wf_const_ind2 := Induction for wf_const Sort Prop
  with wf_const_list_ind2 := Induction for wf_const_list Sort Prop.

Combined Scheme wf_const_mutind from wf_const_ind2, wf_const_list_ind2.

Definition const2GV_isnt_stuck_Prop S TD c t (H:wf_const S TD c t) := 
  forall gl,
  Constant.feasible_typ TD t ->
  wf_global TD S gl ->
  exists gv, _const2GV TD gl c = Some (gv, t).

Definition consts2GV_isnt_stuck_Prop sdct (H:wf_const_list sdct) := 
  let 'lsdct := unmake_list_system_targetdata_const_typ sdct in
  let '(lsdc, lt) := split lsdct in
  let '(lsd, lc) := split lsdc in
  let '(ls, ld) := split lsd in
  forall S TD gl, 
  wf_list_targetdata_typ S TD gl lsd ->
  Constant.feasible_typs TD (make_list_typ lt) ->
  (forall t, (forall t0, In t0 lt -> t0 = t) ->
    exists gv, _list_const_arr2GV TD gl t (make_list_const lc) = Some gv) /\
  (exists gv, _list_const_struct2GV TD gl (make_list_const lc) = 
    Some (gv, (make_list_typ lt))).

Lemma const2GV_isnt_stuck_mutind : 
  (forall S td c t H, @const2GV_isnt_stuck_Prop S td c t H) /\
  (forall sdct H, @consts2GV_isnt_stuck_Prop sdct H).
Proof.
  (wfconst_cases (apply wf_const_mutind with
    (P  := const2GV_isnt_stuck_Prop)
    (P0 := consts2GV_isnt_stuck_Prop)) Case);
    unfold const2GV_isnt_stuck_Prop, consts2GV_isnt_stuck_Prop;
    intros; subst; simpl; eauto.
Case "wfconst_zero".
  destruct (@wf_zeroconst2GV_total targetdata5 typ5) as [gv J]; auto.
  rewrite J. eauto.
Case "wfconst_floatingpoint". 
  inv w; eauto.
Case "wfconst_undef".
  eapply gundef__total in H; eauto.
  destruct H as [gv H].
  rewrite H. eauto.
Case "wfconst_array".
  remember (split
             (unmake_list_system_targetdata_const_typ
                (make_list_system_targetdata_const_typ
                   (map_list_const
                      (fun const_ : LLVMsyntax.const => 
                        (system5, targetdata5, const_, typ5))
                      const_list)))) as R.
  destruct R as [lsdc lt].
  remember (split lsdc) as R'.
  destruct R' as [lsd lc].
  remember (split lsd) as R''.
  destruct R'' as [ls ld].
  destruct (@H system5 targetdata5 gl) as [J1 [gv2 J2]]; 
    try solve [destruct targetdata5; eauto using const2GV_typsize_mutind_array].

    eapply make_list_const_spec1; eauto.

    assert (make_list_const lc = const_list) as EQ.
      eapply make_list_const_spec2; eauto.
    rewrite e. rewrite <- EQ. unfold Size.to_nat in *. 
    destruct (@J1 typ5) as [gv1 J3]; eauto using make_list_const_spec4.
    rewrite J3.
    destruct sz5; eauto.

Case "wfconst_struct".
  remember (split
             (unmake_list_system_targetdata_const_typ
                (make_list_system_targetdata_const_typ
                   (map_list_const_typ
                     (fun (const_ : LLVMsyntax.const) (typ_ : LLVMsyntax.typ) => 
                        (system5, targetdata5, const_, typ_))
                      const_typ_list)))) as R.
  destruct R as [lsdc lt].
  remember (split lsdc) as R'.
  destruct R' as [lsd lc].
  remember (split lsd) as R''.
  destruct R'' as [ls ld].
  destruct (@H system5 targetdata5 gl) as [_ [gv2 J2]];
    try solve [destruct targetdata5; eauto using const2GV_typsize_mutind_struct].

    eapply map_list_const_typ_spec3; eauto.

    erewrite <- map_list_const_typ_spec2; eauto.
    erewrite <- map_list_const_typ_spec1; eauto.
    rewrite J2. 
    destruct gv2; eauto.

Case "wfconst_gid".
  apply H0 in e.  
  destruct e as [gv [sz [e [J1 J2]]]].
  rewrite e. eauto.
Case "wfconst_trunc_int".
  inv f.
  eapply H in H1; eauto.
  destruct H1 as [gv H1].
  rewrite H1.
  unfold mtrunc.
  assert (exists gv, gundef targetdata5 (typ_int sz2) = Some gv) as J.
    eapply gundef__total; eauto.
  destruct J as [gv0 J].
  rewrite J.
  destruct (GV2val targetdata5 gv); eauto.
  destruct v; eauto.
Case "wfconst_trunc_fp".
  inv f.
  eapply H in H1; eauto.
  destruct H1 as [gv H1].
  rewrite H1.
  unfold mtrunc. rewrite e.
  assert (exists gv, gundef targetdata5 (typ_floatpoint floating_point2) = 
           Some gv) as J.
    eapply gundef__total; eauto.
  destruct J as [gv0 J].
  rewrite J.
  destruct (GV2val targetdata5 gv); eauto.
  destruct v; eauto.
  destruct floating_point2; try solve [eauto | inversion w0].
Case "wfconst_zext".
  inv f.
  eapply H in H1; eauto.
  destruct H1 as [gv H1].
  rewrite H1.
  unfold mext.
  assert (exists gv, gundef targetdata5 (typ_int sz2) = Some gv) as J.
    eapply gundef__total; eauto.
  destruct J as [gv0 J].
  rewrite J.
  destruct (GV2val targetdata5 gv); eauto.
  destruct v; eauto.
Case "wfconst_sext".
  inv f.
  eapply H in H1; eauto.
  destruct H1 as [gv H1].
  rewrite H1.
  unfold mext.
  assert (exists gv, gundef targetdata5 (typ_int sz2) = Some gv) as J.
    eapply gundef__total; eauto.
  destruct J as [gv0 J].
  rewrite J.
  destruct (GV2val targetdata5 gv); eauto.
  destruct v; eauto.
Case "wfconst_fpext".
  inv f.
  eapply H in H1; eauto.
  destruct H1 as [gv H1].
  rewrite H1.
  unfold mext.
  assert (exists gv, gundef targetdata5 (typ_floatpoint floating_point2) = 
    Some gv) as J.
    eapply gundef__total; eauto.
  destruct J as [gv0 J].
  rewrite J.
  rewrite e.
  destruct (GV2val targetdata5 gv); eauto.
  destruct v; eauto.
  destruct floating_point2; try solve [eauto | inversion w0].
Case "wfconst_ptrtoint".
  inv f.
  eapply H in H1; eauto.
  destruct H1 as [gv H1].
  rewrite H1. 
  assert (exists gv, gundef targetdata5 (typ_int sz5) = 
    Some gv) as J.
    eapply gundef__total; eauto.
  destruct J as [gv0 J].
  rewrite J. eauto.
Case "wfconst_inttoptr".
  inv f.
  eapply H in H1; eauto.
  destruct H1 as [gv H1].
  rewrite H1.
  assert (exists gv, gundef targetdata5 (typ_pointer typ5) = 
    Some gv) as J.
    eapply gundef__total; eauto.
  destruct J as [gv0 J].
  rewrite J. eauto.
Case "wfconst_bitcast".
  inv f. unfold mbitcast.
  eapply H in H1; eauto.
  destruct H1 as [gv H1].
  rewrite H1. eauto.
Case "wfconst_gep".
  clear H0.
  inv f.
  eapply H in H2; eauto.
  destruct H2 as [gv H2].
  rewrite H2. rewrite e0.
  assert (exists gv, gundef targetdata5 typ' = Some gv) as J.
    eapply gundef__total; eauto.
  destruct J as [gv0 J].
  rewrite J.
  destruct (GV2ptr targetdata5 (getPointerSize targetdata5) gv); eauto.
  destruct (intConsts2Nats targetdata5 const_list); eauto.
  destruct (mgep targetdata5 typ5 v l0); eauto.
Case "wfconst_select".
  assert (J:=H2).
  eapply H0 in H2; eauto.
  destruct H2 as [gv H2].
  rewrite H2. 
  eapply H1 in J; eauto.
  destruct J as [gv' J].
  rewrite J. 
  inv f.
  eapply H in H4; eauto.
  destruct H4 as [gv'' H4].
  rewrite H4.
  destruct (isGVZero targetdata5 gv''); eauto.
Case "wfconst_icmp".
  inv f.
  assert (J:=H3).
  eapply H in H3; eauto.
  destruct H3 as [gv H3].
  rewrite H3. 
  eapply H0 in J; eauto.
  destruct J as [gv' J].
  rewrite J. 
  unfold micmp.
  unfold isPointerTyp in o. unfold is_true in o.
  unfold micmp_int.
  assert (exists gv, gundef targetdata5 (typ_int 1%nat) = 
           Some gv) as JJ.
    eapply gundef__total; eauto.
  destruct JJ as [gv0 JJ].
  rewrite JJ.
  destruct o as [o | o].
    destruct typ5; try solve [simpl in o; contradict o; auto].
    destruct (GV2val targetdata5 gv); eauto.
    destruct v; eauto.
    destruct (GV2val targetdata5 gv'); eauto.
    destruct v; eauto.
    destruct cond5; eauto.

    destruct typ5; try solve [eauto | simpl in o; contradict o; auto].
Case "wfconst_fcmp".
  inv f.
  assert (J:=H3).
  eapply H in H3; eauto.
  destruct H3 as [gv H3].
  rewrite H3. 
  eapply H0 in J; eauto.
  destruct J as [gv' J].
  rewrite J. 
  unfold mfcmp.
  assert (exists gv, gundef targetdata5 (typ_int 1%nat) = 
           Some gv) as JJ.
    eapply gundef__total; eauto.
  destruct JJ as [gv0 JJ].
  rewrite JJ.
  destruct (GV2val targetdata5 gv); eauto.
  destruct v; eauto.
  destruct (GV2val targetdata5 gv'); eauto.
  destruct v; eauto.
  destruct floating_point5; try solve [eauto | inversion w1].
    destruct fcond5; try solve [eauto | inversion e].
    destruct fcond5; try solve [eauto | inversion e].
Case "wfconst_extractvalue".
  inv f.
  eapply H in H3; eauto.
  destruct H3 as [gv H3].
  rewrite H3.
  destruct e0 as [idxs [o [J1 J2]]].
  erewrite mgetoffset__getSubTypFromConstIdxs; eauto.
  unfold LLVMgv.extractGenericValue.
  rewrite J1. rewrite J2.
  destruct (mget targetdata5 gv o typ'); eauto.
    eapply gundef__total in H1; eauto.
    destruct H1. rewrite H1. eauto.
Case "wfconst_insertvalue".
  inv f.
  assert (J:=H2).
  eapply H in H2; eauto.
  destruct H2 as [gv H2].
  rewrite H2.
  eapply H0 in H4; eauto.
  destruct H4 as [gv' H4].
  rewrite H4.
  unfold LLVMgv.insertGenericValue.
  destruct e0 as [idxs [o [J1 J2]]].
  rewrite J1. rewrite J2.
  destruct (mset targetdata5 gv o typ' gv'); eauto.
    eapply gundef__total in J; eauto.
    destruct J as [gv0 J]. rewrite J. eauto.
Case "wfconst_bop".
  assert (exists gv, gundef targetdata5 (typ_int sz5) = Some gv) as JJ.
    eapply gundef__total; eauto.
  destruct JJ as [gv0 JJ].
  assert (J:=H1).
  eapply H in H1; eauto.
  destruct H1 as [gv H1].
  rewrite H1.
  eapply H0 in J; eauto.
  destruct J as [gv' J].
  rewrite J.
  unfold mbop, Size.to_nat. 
  rewrite JJ.
  destruct (GV2val targetdata5 gv); eauto.
  destruct (GV2val targetdata5 gv'); eauto.
  destruct v; eauto.
  destruct v0; eauto.
  destruct (eq_nat_dec (wz + 1) sz5); eauto.
  destruct bop5; eauto.
  destruct v; eauto.
Case "wfconst_fbop".
  assert (exists gv, gundef targetdata5 (typ_floatpoint floating_point5) 
    = Some gv) as JJ.
    eapply gundef__total; eauto.
  destruct JJ as [gv0 JJ].
  assert (J:=H1).
  eapply H in H1; eauto.
  destruct H1 as [gv H1].
  rewrite H1.
  eapply H0 in J; eauto.
  destruct J as [gv' J].
  rewrite J.
  unfold mfbop. rewrite JJ.
  destruct (GV2val targetdata5 gv); eauto.
  destruct (GV2val targetdata5 gv'); eauto.
  destruct v; eauto.
  destruct v0; eauto.
  destruct floating_point5; try solve [eauto | inversion w1].
  destruct v; eauto.
Case "wfconst_cons".
  remember (split (unmake_list_system_targetdata_const_typ l')) as R1.
  destruct R1 as [lsdc lt].
  simpl.  
  remember (split lsdc) as R2.
  destruct R2 as [lsd lc].
  simpl.  
  remember (split lsd) as R3.
  destruct R3 as [ls ld].
  simpl.
  intros S TD gl Hwfl Hft.
  assert (Constant.feasible_typs TD (make_list_typ lt) /\
          Constant.feasible_typ TD typ5) as J.
    clear - Hft.
    destruct Hft.
    split; auto.
  destruct J as [J1 J2].
  assert (wf_list_targetdata_typ S TD gl lsd /\ system5 = S /\ targetdata5 = TD
            /\ wf_global TD S gl) 
    as Hwfl'.
    clear - Hwfl.
    unfold wf_list_targetdata_typ in *.
    assert (In (system5, targetdata5) ((system5, targetdata5) :: lsd)) as J.
      simpl. auto.
    apply Hwfl in J. 
    destruct J as [J1 [J2 J3]]; subst.
    split.
      intros S1 TD1 Hin.    
      apply Hwfl. simpl. auto.
    split; auto.

  destruct Hwfl' as [Hwfl' [Heq1 [Heq2 Hwfg]]]; subst.  
  assert (J2':=J2).
  eapply H in J2'; eauto.
  destruct J2' as [gv J2'].
  rewrite J2'.
  assert (J1':=J1).
  eapply H0 in J1'; eauto.
  destruct J1' as [J1' [g2 J12]].
  rewrite J12.
  apply feasible_typ_inv'' in J2.  
  destruct J2 as [ssz [asz [J21 J22]]].
  rewrite J22.
  split; eauto.  
    intros.
    destruct (@J1' t) as [gv0 H2]; eauto.
    rewrite H2.
    assert (typ5 = t) as EQ. apply H1; auto.
    subst.
    destruct (typ_dec t t); eauto.
      contradict n; auto.
Qed.

Lemma mbop_is_total : forall S TD bop0 sz0, 
  wf_typ S (typ_int sz0) ->
  feasible_typ TD (typ_int sz0) ->
  forall x y, exists z, mbop TD bop0 sz0 x y = Some z.
Proof.
  intros S TD bop0 sz0 Hwft Hft x y.
  unfold mbop. inv Hft.
  destruct (GV2val TD x); eauto using gundef__total.
  destruct v; eauto using gundef__total.
  destruct (GV2val TD y); eauto using gundef__total.
  destruct v; eauto using gundef__total.
  destruct (eq_nat_dec (wz + 1) (Size.to_nat sz0)); 
    eauto using gundef__total.
  destruct bop0; eauto using gundef__total.
Qed.

Lemma mfbop_is_total : forall S TD fbop0 fp, 
  wf_typ S (typ_floatpoint fp) ->
  feasible_typ TD (typ_floatpoint fp) ->
  forall x y, exists z, mfbop TD fbop0 fp x y = Some z.
Proof.
  intros.
  unfold mfbop. inv H0.
  destruct (GV2val TD x); eauto using gundef__total.
  destruct v; eauto using gundef__total.
  destruct (GV2val TD y); eauto using gundef__total.
  destruct v; eauto using gundef__total.
  destruct fp; try solve [eauto | inversion H].
Qed.

Lemma micmp_is_total : forall TD c t, 
  Typ.isIntOrIntVector t \/ isPointerTyp t ->
  forall x y, exists z, micmp TD c t x y = Some z.
Proof.
  intros TD c t Hwft x y.
  unfold micmp, micmp_int.
  unfold isPointerTyp in Hwft. unfold is_true in Hwft.
  unfold micmp_int.
  destruct Hwft as [Hwft | Hwft].
    destruct t; try solve [simpl in Hwft; contradict Hwft; auto].
    destruct (GV2val TD x); eauto using gundef_i1__total.
    destruct v; eauto using gundef_i1__total.
    destruct (GV2val TD y); eauto using gundef_i1__total.
    destruct v; eauto using gundef_i1__total.
    destruct c; eauto using gundef_i1__total.
  
    destruct t; try solve [simpl in Hwft; contradict Hwft; auto]. 
      eauto using gundef_i1__total.
Qed.

Lemma mfcmp_is_total : forall S TD c fp, 
  wf_fcond c = true  ->
  wf_typ S (typ_floatpoint fp) ->
  feasible_typ TD (typ_floatpoint fp) ->
  forall x y, exists z, mfcmp TD c fp x y = Some z.
Proof.
  intros S TD c fp Hc Ht Hft2 x y.
  unfold mfcmp.
  destruct (GV2val TD x); eauto using gundef_i1__total.
  destruct v; eauto using gundef_i1__total.
  destruct (GV2val TD y); eauto using gundef_i1__total.
  destruct v; eauto using gundef_i1__total.
  destruct fp; try solve [eauto | inversion Ht].
    destruct c; try solve [eauto | inversion Hc].
    destruct c; try solve [eauto | inversion Hc].
Qed.

Lemma GEP_is_total : forall TD t mp vidxs inbounds0,
  exists mp', LLVMgv.GEP TD t mp vidxs inbounds0 = ret mp'.
Proof.
  intros. unfold LLVMgv.GEP.
  destruct (GV2ptr TD (getPointerSize TD) mp); eauto using gundef_p1__total.
  destruct (GVs2Nats TD vidxs); eauto using gundef_p1__total.
  destruct (mgep TD t v l0); eauto using gundef_p1__total.
Qed.

Lemma mcast_is_total : forall ifs s f b los nts ps id5 cop0 t1 t2 v,
  wf_cast ifs s (module_intro los nts ps) f b 
    (insn_cmd (insn_cast id5 cop0 t1 v t2)) ->
  forall x, exists z, mcast (los,nts) cop0 t1 t2 x = Some z.
Proof.
  intros.
  unfold mcast, mbitcast.
  inv H; eauto using gundef__total'.
Qed.

Lemma mtrunc_is_total : forall ifs s f b los nts ps id5 top0 t1 t2 v, 
  wf_trunc ifs s (module_intro los nts ps) f b 
    (insn_cmd (insn_trunc id5 top0 t1 v t2)) ->
  forall x, exists z, mtrunc (los,nts) top0 t1 t2 x = Some z.
Proof.
  intros.
  assert (J:=H).
  apply wf_trunc__wf_typ in J.
  destruct J as [J1 J2]. inv J2.
  unfold mtrunc.
  destruct (GV2val (los, nts) x); eauto using gundef__total.
  inv H; try solve [destruct v0; eauto using gundef__total].
    rewrite H16.
    destruct v0; eauto using gundef__total.
      destruct floating_point2; try solve [eauto | inversion H14].
Qed.

Lemma mext_is_total : forall ifs s f b los nts ps id5 eop0 t1 t2 v, 
  wf_ext ifs s (module_intro los nts ps) f b 
    (insn_cmd (insn_ext id5 eop0 t1 v t2)) ->
  forall x,  exists z, mext (los,nts) eop0 t1 t2 x = Some z.
Proof.
  intros.
  unfold mext.
  inv H; try solve 
    [destruct (GV2val (los, nts) x); eauto using gundef__total'; 
     destruct v0; eauto using gundef__total'].
    rewrite H15.
    destruct (GV2val (los, nts) x); eauto using gundef__total'; 
    destruct v0; eauto using gundef__total'.
    destruct floating_point2; try solve [inversion H13 | eauto].
Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)
