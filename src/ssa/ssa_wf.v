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

Export LLVMgv.
Export LLVMopsem.

(* The relation says that any value can be of any typ, which is exactly true
   for an LLVM that allows cast between any pointer types. Type safety needs 
   a subtyping relation w.r.t data type layout. *)
Inductive wf_genericvalue : TargetData -> GenericValue -> typ -> Prop :=
| wf_genericvalue_intro : forall TD gv t sz, 
    getTypeSizeInBits TD t = Some sz ->
    sizeGenericValue gv = Coqlib.nat_of_Z (Coqlib.ZRdiv (Z_of_nat sz) 8) ->
    wf_genericvalue TD gv t.

Hint Constructors wf_genericvalue.

Inductive wf_defs TD (f:fdef) (lc:GVMap) : list atom -> Prop :=
| wf_defs_nil : wf_defs TD f lc nil
| wf_defs_cons : forall id1 t1 gv1 defs',
    lookupTypViaIDFromFdef f id1 = Some t1 ->
    lookupAL _ lc id1 = Some gv1 ->
    wf_genericvalue TD gv1 t1 ->
    wf_defs TD f lc defs' ->
    wf_defs TD f lc (id1::defs').

Lemma wf_defs_elim : forall TD ids1 F lc,
  wf_defs TD F lc ids1 ->
  forall id1, In id1 ids1 ->
  exists t1, exists gv1,
    lookupTypViaIDFromFdef F id1 = Some t1 /\
    lookupAL _ lc id1 = Some gv1 /\
    wf_genericvalue TD gv1 t1.
Proof.
  induction ids1; intros; simpl in H0; inv H0.  
    inv H.
    exists t1. exists gv1. split; auto.

    inv H.
    eapply IHids1 in H6; eauto.
Qed.    

Lemma wf_defs_intro : forall TD ids1 F lc,
  (forall id1, In id1 ids1 ->
   exists t1, exists gv1,
     lookupTypViaIDFromFdef F id1 = Some t1 /\
     lookupAL _ lc id1 = Some gv1 /\
     wf_genericvalue TD gv1 t1) ->
  wf_defs TD F lc ids1.
Proof.
  induction ids1; intros.
    apply wf_defs_nil.  

    destruct (@H a) as [t1 [gv1 [J1 [J2 J3]]]]; simpl; auto.
    eapply wf_defs_cons; eauto.
      apply IHids1.
      intros id1 J.
      apply H. simpl. auto.
Qed.

Lemma wf_defs_eq : forall TD ids2 ids1 F' lc',
  set_eq _ ids1 ids2 ->
  wf_defs TD F' lc' ids1 ->
  wf_defs TD F' lc' ids2.
Proof.
  intros.
  apply wf_defs_intro.
  intros id1 Hin.
  destruct H as [J1 J2].
  eapply wf_defs_elim in H0; eauto.
Qed.

Lemma wf_defs_updateAddAL : forall TD g F' lc' ids1 ids2 i1 t1,
  wf_defs TD F' lc' ids1 ->
  set_eq _ (i1::ids1) ids2 ->
  lookupTypViaIDFromFdef F' i1 = ret t1 ->
  wf_genericvalue TD g t1 ->
  wf_defs TD F' (updateAddAL GenericValue lc' i1 g) ids2.
Proof.
  intros TD g F' lc' ids1 ids2 i1 t1 HwfDefs Heq Hlkup Hgv.  
  apply wf_defs_intro.  
  intros id1 Hin.
  destruct Heq as [Hinc1 Hinc2].
  apply Hinc2 in Hin.
  simpl in Hin.
  destruct (eq_dec i1 id1); subst.
    exists t1. exists g. 
    split; auto.
    split; auto. 
      apply lookupAL_updateAddAL_eq; auto.      

    destruct Hin as [Eq | Hin]; subst; try solve [contradict n; auto].
    eapply wf_defs_elim in HwfDefs; eauto.
    destruct HwfDefs as [t2 [gv2 [J1 [J2 J3]]]].
    exists t2. exists gv2.
    split; auto.
    split; auto. 
      rewrite <- lookupAL_updateAddAL_neq; auto.      
Qed.

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

Definition wf_lc TD (f:fdef) (lc:GVMap) : Prop := forall i0 gv0 t0, 
  lookupTypViaIDFromFdef f i0 = Some t0 ->
  lookupAL _ lc i0 = Some gv0 -> wf_genericvalue TD gv0 t0.

Lemma getOperandValue__wf_gv : forall los nts s ps f v t lc gl gv,
  wf_global (los,nts) s gl ->
  wf_lc (los,nts) f lc ->
  wf_value s (module_intro los nts ps) f v t ->
  getOperandValue (los,nts) v lc gl = Some gv ->
  wf_genericvalue (los,nts) gv t.
Proof.
  intros los nts s ps f v t lc gl gv Hwfg Hwflc Hwfv Hget.
  inv Hwfv;  simpl in Hget. 
    inv H7. eapply const2GV__getTypeSizeInBits in Hget; eauto.
    destruct Hget as [sz [J1 J2]].
    eapply wf_genericvalue_intro; eauto.

    unfold wf_lc in Hwflc.
    eapply Hwflc in H8; eauto.
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

Lemma getIncomingValuesForBlockFromPHINodes_spec1_aux : forall ifs s Ps los nts f
    b gl lc id1 t l3 cs tmn ps2 ps1 lc' ,
  wf_lc (los,nts) f lc ->
  Some lc' = getIncomingValuesForBlockFromPHINodes (los,nts) ps2 b gl lc ->
  In id1 (getPhiNodesIDs ps2) ->
  uniqFdef f ->
  blockInFdefB (block_intro l3 (ps1++ps2) cs tmn) f ->
  wf_global (los, nts) s gl ->
  wf_phinodes ifs s (module_intro los nts Ps) f 
    (block_intro l3 (ps1++ps2) cs tmn) ps2 ->
  lookupTypViaIDFromFdef f id1 = ret t ->
  exists gv, lookupAL _ lc' id1 = Some gv /\ wf_genericvalue (los,nts) gv t.
Proof.    
  intros ifs s Ps los nts f b gl lc id1 t l3 cs tmn ps2 ps1 lc' Hwflc H H0 Huniq 
    Hbinf Hwfg Hwfps Hlk.
  assert (Huniq':=Hbinf).
  apply uniqFdef__uniqBlockLocs in Huniq'; auto.
  simpl in Huniq'. 
  apply NoDup_split in Huniq'.
  destruct Huniq' as [Huniq' _].
  assert (In id1 (getPhiNodesIDs (ps1++ps2))) as Hin.
    rewrite getPhiNodesIDs_app.
    apply in_app_iff; auto.
  generalize dependent lc'.
  generalize dependent ps1.
  induction ps2; simpl in *; intros.
    inversion H0.

    assert (J:=Hbinf).
    eapply lookupTypViaIDFromFdef__lookupTypViaIDFromPhiNodes in J; eauto.
    destruct a.
    simpl in H0. simpl in J.
    inv Hwfps. inv H8.
    destruct H0 as [H0 | H0]; subst.
      rewrite NoDup_lookupTypViaIDFromPhiNodes in J; auto.
      inv J.
      remember (getValueViaBlockFromValuels l0 b) as R0.
      destruct R0; try solve [inversion H].
        eapply wf_value_list__getValueViaBlockFromValuels__wf_value in H4; eauto.
        remember (getOperandValue (los,nts) v lc gl) as R.
        destruct R; tinv H.
        symmetry in HeqR. eapply getOperandValue__wf_gv in HeqR; eauto.
        destruct (getIncomingValuesForBlockFromPHINodes (los,nts) ps2 b gl lc); 
          inv H.
        exists g. simpl. 
        destruct (id1 == id1) as [e' | n]; try solve [contradict n; auto].
          split; auto.

      remember (getValueViaBlockFromValuels l0 b) as R0.
      destruct R0; try solve [inversion H].   
        remember (getOperandValue (los,nts) v lc gl) as R.
        destruct R; tinv H. 
        remember (getIncomingValuesForBlockFromPHINodes (los,nts) ps2 b gl lc) 
          as R.
        destruct R; inversion H; subst.         
        simpl.
        destruct (id1==i0); subst.
          clear - Huniq' H0.
          rewrite getPhiNodesIDs_app in Huniq'.
          apply NoDup_split in Huniq'.
          destruct Huniq' as [_ Huniq'].
          inv Huniq'. congruence.
      
          eapply IHps2 with (ps1:=ps1 ++ [insn_phi i0 t0 l0]); simpl_env; eauto.
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

Lemma getIncomingValuesForBlockFromPHINodes_spec1 : forall ifs s Ps los nts f b 
    gl lc id1 t l3 cs tmn ps lc' ,
  wf_lc (los,nts) f lc ->
  Some lc' = getIncomingValuesForBlockFromPHINodes (los,nts) ps b gl lc ->
  In id1 (getPhiNodesIDs ps) ->
  uniqFdef f ->
  Some (block_intro l3 ps cs tmn) = lookupBlockViaLabelFromFdef f l3 ->
  wf_global (los, nts) s gl ->
  wf_fdef ifs s (module_intro los nts Ps) f ->
  lookupTypViaIDFromFdef f id1 = ret t ->
  exists gv, lookupAL _ lc' id1 = Some gv /\ wf_genericvalue (los,nts) gv t.
Proof.
  intros.
  assert (blockInFdefB (block_intro l3 ps cs tmn) f) as Hbinf.
    symmetry in H3.
    apply lookupBlockViaLabelFromFdef_inv in H3; auto.
    destruct H3; eauto.
  eapply getIncomingValuesForBlockFromPHINodes_spec1_aux with (ps1:=nil); 
    eauto using wf_fdef__wf_phinodes.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_spec2_aux : forall ifs s los nts Ps f
  b gl lc l3 cs tmn (Hwflc: wf_lc (los, nts) f lc) 
  (Hwfg: wf_global (los, nts) s gl) (Huniq: uniqFdef f) ps2 ps1 rs,
  blockInFdefB (block_intro l3 (ps1++ps2) cs tmn) f ->
  wf_phinodes ifs s (module_intro los nts Ps) f 
    (block_intro l3 (ps1++ps2) cs tmn) ps2 ->
  Some rs = getIncomingValuesForBlockFromPHINodes (los, nts) ps2 b gl lc ->
  (forall id0 gv t0, In (id0,gv) rs -> lookupTypViaIDFromFdef f id0 = Some t0 ->
     wf_genericvalue (los, nts) gv t0).
Proof.    
  intros ifs s los nts Ps f b gl lc l3 cs tmn Hwflc Hwfg Huniq ps2 ps1 rs Hbinf.
  assert (Huniq':=Hbinf).
  apply uniqFdef__uniqBlockLocs in Huniq'; auto.
  simpl in Huniq'. 
  apply NoDup_split in Huniq'.
  destruct Huniq' as [Huniq' _].
  generalize dependent rs.
  generalize dependent ps1.
  induction ps2; intros ps1 Hbinf Hnup rs Hwfps H id0 gv t0 Hin Hlkup; 
    simpl in *.
    inv H. inv Hin.

    destruct a.
    remember (getValueViaBlockFromValuels l0 b) as R1.
    destruct R1; try solve [inversion H].   
      remember (getOperandValue (los,nts) v lc gl) as R.
      destruct R; tinv H.
      destruct (getIncomingValuesForBlockFromPHINodes (los,nts) ps2 b gl lc); 
        inv H.
      inv Hwfps.
      simpl in Hin. 
      destruct Hin as [Hin | Hin]; eauto.
        inv Hin.
        inv H6.
        assert (J:=Hbinf).
        eapply lookupTypViaIDFromFdef__lookupTypViaIDFromPhiNodes in J; eauto.
          eapply wf_value_list__getValueViaBlockFromValuels__wf_value in H2; 
            eauto.
          simpl in J.
          rewrite NoDup_lookupTypViaIDFromPhiNodes in J; auto.
          inv J.
          symmetry in HeqR. eapply getOperandValue__wf_gv in HeqR; eauto.

          simpl. rewrite getPhiNodesIDs_app.
          apply in_app_iff; simpl; auto.

        rewrite_env ((ps1 ++ [insn_phi i0 t l0]) ++ ps2) in H7.
        eapply IHps2 in H7; simpl_env; eauto.
Qed.

Lemma getIncomingValuesForBlockFromPHINodes_spec2 : forall ifs s los nts Ps f b 
  gl lc l3 cs tmn (Hwflc: wf_lc (los, nts) f lc) 
  (Hwfg: wf_global (los, nts) s gl) (Huniq: uniqFdef f) ps rs,
  Some (block_intro l3 ps cs tmn) = lookupBlockViaLabelFromFdef f l3 ->
  wf_global (los, nts) s gl ->
  wf_fdef ifs s (module_intro los nts Ps) f ->
  Some rs = getIncomingValuesForBlockFromPHINodes (los, nts) ps b gl lc ->
  (forall id0 gv t0, In (id0,gv) rs -> lookupTypViaIDFromFdef f id0 = Some t0 ->
     wf_genericvalue (los, nts) gv t0).
Proof.
  intros.
  assert (blockInFdefB (block_intro l3 ps cs tmn) f) as Hbinf.
    symmetry in H.
    apply lookupBlockViaLabelFromFdef_inv in H; auto.
    destruct H; eauto.
  eapply getIncomingValuesForBlockFromPHINodes_spec2_aux with (ps1:=nil); 
    eauto using wf_fdef__wf_phinodes.
Qed.

Lemma updateValuesForNewBlock_spec2 : forall TD f lc id1 gv t,
  lookupAL _ lc id1 = Some gv ->
  lookupTypViaIDFromFdef f id1 = Some t ->
  wf_lc TD f lc ->
  forall rs, 
  (forall id0 gv t0, 
     In (id0,gv) rs -> lookupTypViaIDFromFdef f id0 = Some t0 ->
     wf_genericvalue TD gv t0) ->
  exists t', exists gv', 
    lookupTypViaIDFromFdef f id1 = Some t' /\
    lookupAL _ (updateValuesForNewBlock rs lc) id1 = Some gv' /\
    wf_genericvalue TD gv' t'.
Proof.
  induction rs; intros; simpl in *.   
    exists t. exists gv. eauto.

    destruct a. 
    destruct (id1==i0); subst.
      exists t. exists g. rewrite lookupAL_updateAddAL_eq; eauto.
      rewrite <- lookupAL_updateAddAL_neq; eauto.
Qed.

Lemma updateValuesForNewBlock_spec3 : forall TD f lc,
  wf_lc TD f lc ->
  forall rs, 
  (forall id0 gv t0, 
     In (id0,gv) rs -> lookupTypViaIDFromFdef f id0 = Some t0 ->
     wf_genericvalue TD gv t0) ->
  wf_lc TD f (updateValuesForNewBlock rs lc).
Proof.  
  induction rs; intros; simpl in *; auto.
    destruct a.
    intros x gvx tx Htyp Hlk.
    destruct (i0==x); subst.
      rewrite lookupAL_updateAddAL_eq in Hlk. inv Hlk. eauto.

      rewrite <- lookupAL_updateAddAL_neq in Hlk; auto.
      eapply IHrs in Hlk; eauto.
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

Lemma wf_lc_br_aux : forall ifs s los nts Ps f b1 b2 gl lc lc' l3 
  (Hwfg: wf_global (los, nts) s gl) (Huniq: uniqFdef f)
  (Hswitch : switchToNewBasicBlock (los, nts) b1 b2 gl lc = ret lc')
  (Hlkup : Some b1 = lookupBlockViaLabelFromFdef f l3)
  (Hwfg : wf_global (los, nts) s gl)
  (HwfF : wf_fdef ifs s (module_intro los nts Ps) f)
  (Hwflc : wf_lc (los, nts) f lc),
  wf_lc (los, nts) f lc'.
Proof.
  intros.
  unfold switchToNewBasicBlock in Hswitch. simpl in Hswitch.
  remember (getIncomingValuesForBlockFromPHINodes (los, nts)
              (getPHINodesFromBlock b1) b2 gl lc) as R1.
  destruct R1; inv Hswitch.
  apply updateValuesForNewBlock_spec3; auto.
    destruct b1.
    eapply getIncomingValuesForBlockFromPHINodes_spec2; 
      eauto using lookupBlockViaLabelFromFdef_prop.
Qed.

Lemma wf_defs_br_aux : forall lc l' ps' cs' lc' F tmn' gl los nts Ps ifs s
  (l3 : l)
  (ps : phinodes)
  (cs : list cmd) tmn
  (Hlkup : Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l')
  (Hswitch : switchToNewBasicBlock (los,nts) (block_intro l' ps' cs' tmn')
         (block_intro l3 ps cs tmn) gl lc = ret lc')
  (t : list atom)
  (Hwfdfs : wf_defs (los,nts) F lc t)
  (ids0' : list atom)
  (Hwflc : wf_lc (los,nts) F lc)
  (Hwfg : wf_global (los, nts) s gl)
  (HwfF : wf_fdef ifs s (module_intro los nts Ps) F)
  (Huniq : uniqFdef F)
  (Hinc : incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) t),
  wf_defs (los,nts) F lc' ids0'.
Proof.
  intros.
  unfold switchToNewBasicBlock in Hswitch. simpl in Hswitch.
  apply wf_defs_intro.
  intros id1 Hid1.
  remember (getIncomingValuesForBlockFromPHINodes (los,nts) ps'
                (block_intro l3 ps cs tmn) gl lc) as R1.
  destruct R1; inv Hswitch.
  destruct (In_dec eq_atom_dec id1 (getPhiNodesIDs ps')) as [Hin | Hnotin].
    assert (J:=Hlkup).
    eapply InPhiNodes_lookupTypViaIDFromFdef in Hlkup; eauto.
    destruct Hlkup as [t1 Hlkup].
    eapply getIncomingValuesForBlockFromPHINodes_spec1 in HeqR1; eauto.
    destruct HeqR1 as [gv [HeqR1 Hwfgv]].
    apply updateValuesForNewBlock_spec1 with (lc:=lc) in HeqR1.
    exists t1. exists gv.
    split; auto.

    apply ListSet.set_diff_intro with (x:=ids0')(Aeq_dec:=eq_atom_dec) in Hnotin;
      auto.
    apply Hinc in Hnotin.
    apply wf_defs_elim with (id1:=id1) in Hwfdfs; auto.
    destruct Hwfdfs as [t1 [gv1 [J1 [J2 J3]]]].
    eapply updateValuesForNewBlock_spec2 with (rs:=l0) in J2; eauto.
      eapply getIncomingValuesForBlockFromPHINodes_spec2; eauto.
Qed.

Lemma inscope_of_tmn_br_aux : forall F l3 ps cs tmn ids0 l' ps' cs' tmn' l0 ifs
  s los nts Ps lc lc' gl,
wf_global (los, nts) s gl ->
wf_lc (los,nts) F lc ->
wf_fdef ifs s (module_intro los nts Ps) F ->
uniqFdef F ->
blockInFdefB (block_intro l3 ps cs tmn) F = true ->
In l0 (successors_terminator tmn) ->
Some ids0 = inscope_of_tmn F (block_intro l3 ps cs tmn) tmn ->
Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l0 ->
switchToNewBasicBlock (los,nts) (block_intro l' ps' cs' tmn')
  (block_intro l3 ps cs tmn) gl lc = Some lc' ->
wf_defs (los,nts) F lc ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs (los,nts) F lc' ids0'.
Proof.
  intros F l3 ps cs tmn ids0 l' ps' cs' tmn' l0 ifs s los nts Ps lc lc' gl Hwfg
    Hwflc HwfF Huniq HBinF Hsucc Hinscope Hlkup Hswitch Hwfdfs.
  symmetry in Hlkup.
  assert (J:=Hlkup).
  apply lookupBlockViaLabelFromFdef_inv in J; auto.
  destruct J as [Heq J]; subst.
  unfold inscope_of_tmn in Hinscope.
  unfold inscope_of_tmn. unfold inscope_of_cmd.
  destruct F as [[? ? ? la va] bs].
  remember (dom_analyze (fdef_intro (fheader_intro f t i0 la va) bs)) as Doms.
  remember (Doms !! l3)as defs3.
  remember (Doms !! l')as defs'.
  destruct defs3 as [contents3 inbound3]. 
  destruct defs' as [contents' inbound']. 

  assert (incl contents' (l3::contents3)) as Hsub.
    clear - HBinF Hsucc Heqdefs3 Heqdefs' HeqDoms Huniq HwfF.
    simpl in Huniq. destruct Huniq.
    eapply dom_successors; eauto.

  destruct cs'.
  Case "cs'=nil".
    assert (J1:=inbound').
    apply fold_left__bound_blocks with (init:=getPhiNodesIDs ps' ++ 
      getCmdsIDs nil ++ getArgsIDs la)(t:=t)(i0:=i0)(la:=la)(va:=va)(bs:=bs)
      (fa:=f)(l0:=l') in J1.
    destruct J1 as [r J1].
    exists r. split; auto.

    assert (incl (ListSet.set_diff eq_atom_dec r (getPhiNodesIDs ps')) ids0)
      as Jinc.
      clear - Hinscope J1 Hsub HBinF Huniq.
      apply fold_left__spec in J1.
      symmetry in Hinscope.
      apply fold_left__spec in Hinscope.
      destruct J1 as [J1 [J2 J3]].
      destruct Hinscope as [J4 [J5 J6]].
      intros id1 J.
      assert (J':=J).
      apply ListSet.set_diff_elim1 in J.
      apply ListSet.set_diff_elim2 in J'.
      apply J3 in J.
      destruct J as [J | J].
      SCase "id1 in init and the current block".
        simpl in J.
        apply in_app_or in J.
        destruct J as [J | J]; try solve [contradict J; auto].
        apply J4.
        apply in_or_app. right.
        apply in_or_app; auto.
      SCase "id1 in strict dominating blocks".
        destruct J as [b1 [l1 [J8 [J9 J10]]]].
        assert (In l1 contents') as J8'.
          clear - J8.
          apply ListSet.set_diff_elim1 in J8. auto.
        apply Hsub in J8'.
          destruct (eq_atom_dec l1 l3); subst.
            simpl in J9. 
            assert (b1=block_intro l3 ps cs tmn) as EQ.
              clear - J9 HBinF Huniq. destruct Huniq.
              eapply InBlocksB__lookupAL; eauto.
            subst.
            simpl in J10.
            apply J4.
            rewrite_env 
              ((getPhiNodesIDs ps ++ getCmdsIDs cs) ++ getArgsIDs la).
            apply in_or_app; auto.
      
            apply J5 in J9; auto.
              simpl in J8'.
              destruct J8' as [J8' | J8']; try solve [contradict n; auto].
              apply ListSet.set_diff_intro; auto.
                intro J. simpl in J. 
                destruct J as [J | J]; auto.

    split; auto.
      eapply wf_defs_br_aux; eauto.
        
  Case "cs'<>nil".
    assert (J1:=inbound').
    unfold cmds_dominates_cmd. simpl.
    destruct (eq_atom_dec (getCmdLoc c) (getCmdLoc c)) as [_ | n]; 
      try solve [contradict n; auto].
    simpl_env.
    apply fold_left__bound_blocks with (init:=getPhiNodesIDs ps' ++ 
      getArgsIDs la)(t:=t)(i0:=i0)(la:=la)(va:=va)(bs:=bs)(l0:=l')(fa:=f) in J1.
    destruct J1 as [r J1].
    exists r.  split; auto.

    assert (incl (ListSet.set_diff eq_atom_dec r (getPhiNodesIDs ps')) ids0)
      as Jinc.
      clear - Hinscope J1 Hsub HBinF Huniq.
      apply fold_left__spec in J1.
      symmetry in Hinscope.
      apply fold_left__spec in Hinscope.
      destruct J1 as [J1 [J2 J3]].
      destruct Hinscope as [J4 [J5 J6]].
      intros id1 J.
      assert (J':=J).
      apply ListSet.set_diff_elim1 in J.
      apply ListSet.set_diff_elim2 in J'.
      apply J3 in J.
      destruct J as [J | J].
      SCase "id1 in init and the current block".
        simpl in J.
        apply in_app_or in J.
        destruct J as [J | J]; try solve [contradict J; auto].
        apply J4.
        apply in_or_app. right.
        apply in_or_app; auto.
      SCase "id1 in strict dominating blocks".
        destruct J as [b1 [l1 [J8 [J9 J10]]]].
        assert (In l1 contents') as J8'.
          clear - J8.
          apply ListSet.set_diff_elim1 in J8. auto.
        apply Hsub in J8'.
          destruct (eq_atom_dec l1 l3); subst.
            simpl in J9. 
            assert (b1=block_intro l3 ps cs tmn) as EQ.
              clear - J9 HBinF Huniq. destruct Huniq.
              eapply InBlocksB__lookupAL; eauto.
            subst.
            simpl in J10.
            apply J4.
            rewrite_env 
              ((getPhiNodesIDs ps ++ getCmdsIDs cs) ++ getArgsIDs la).
            apply in_or_app; auto.
      
            apply J5 in J9; auto. 
              simpl in J8'.
              destruct J8' as [J8' | J8']; try solve [contradict n; auto].
              apply ListSet.set_diff_intro; auto.
                intro J. simpl in J. 
                destruct J as [J | J]; auto.

    split; auto.
      eapply wf_defs_br_aux; eauto.
Qed.

Lemma inscope_of_tmn_br_uncond : forall F l3 ps cs ids0 l' ps' cs' tmn' l0 
  ifs s los nts Ps lc lc' gl bid,
wf_global (los, nts) s gl ->
wf_lc (los,nts) F lc ->
wf_fdef ifs s (module_intro los nts Ps) F ->
uniqFdef F ->
blockInFdefB (block_intro l3 ps cs (insn_br_uncond bid l0)) F = true ->
Some ids0 = inscope_of_tmn F (block_intro l3 ps cs (insn_br_uncond bid l0)) 
  (insn_br_uncond bid l0) ->
Some (block_intro l' ps' cs' tmn') = lookupBlockViaLabelFromFdef F l0 ->
switchToNewBasicBlock (los,nts) (block_intro l' ps' cs' tmn')
  (block_intro l3 ps cs (insn_br_uncond bid l0)) gl lc = Some lc' ->
wf_defs (los,nts) F lc ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs (los,nts) F lc' ids0'.
Proof.
  intros.
  eapply inscope_of_tmn_br_aux; eauto.
  simpl. auto.
Qed.

Lemma inscope_of_tmn_br : forall F l0 ps cs bid l1 l2 ids0 l' ps' cs' tmn' Cond 
  c los nts Ps gl lc ifs s lc',
wf_global (los, nts) s gl ->
wf_lc (los,nts) F lc ->
wf_fdef ifs s (module_intro los nts Ps) F ->
uniqFdef F ->
blockInFdefB (block_intro l0 ps cs (insn_br bid Cond l1 l2)) F = true ->
Some ids0 = inscope_of_tmn F (block_intro l0 ps cs (insn_br bid Cond l1 l2)) 
  (insn_br bid Cond l1 l2) ->
getOperandValue (los,nts) Cond lc gl = ret c ->
Some (block_intro l' ps' cs' tmn') =
       (if isGVZero (los,nts) c
        then lookupBlockViaLabelFromFdef F l2
        else lookupBlockViaLabelFromFdef F l1) ->
switchToNewBasicBlock (los,nts) (block_intro l' ps' cs' tmn')
  (block_intro l0 ps cs (insn_br bid Cond l1 l2)) gl lc = Some lc' ->
wf_defs (los,nts) F lc ids0 ->
exists ids0',
  match cs' with
  | nil => Some ids0' = inscope_of_tmn F (block_intro l' ps' cs' tmn') tmn'
  | c'::_ => Some ids0' = inscope_of_cmd F (block_intro l' ps' cs' tmn') c'
  end /\
  incl (ListSet.set_diff eq_atom_dec ids0' (getPhiNodesIDs ps')) ids0 /\
  wf_defs (los,nts) F lc' ids0'.
Proof.
  intros.
  remember (isGVZero (los,nts) c) as R.
  destruct R; eapply inscope_of_tmn_br_aux; eauto; simpl; auto.
Qed.

Fixpoint wf_params TD (gvs:list GenericValue) (lp:params) : Prop :=
match (gvs, lp) with
| (nil, nil) => True
| (gv::gvs', (t, _)::lp') => wf_genericvalue TD gv t /\ wf_params TD gvs' lp'
| _ => False
end.

Lemma params2GVs_wf_gv : forall los nts Ps F gl lc (Hwfc : wf_lc (los,nts) F lc)
  S (Hwfg : wf_global (los, nts) S gl) tvs lp gvs,
  wf_value_list
          (make_list_system_module_fdef_value_typ
             (map_list_typ_value
                (fun (typ_' : typ) (value_'' : value) =>
                 (S, (module_intro los nts Ps), F, value_'', typ_'))
                tvs)) ->
  lp = map_list_typ_value
        (fun (typ_' : typ) (value_'' : value) => (typ_', value_''))
        tvs ->
  params2GVs (los,nts) lp lc gl = Some gvs -> wf_params (los,nts) gvs lp.
Proof.
  induction tvs; intros lp gvs Hwfvs Heq Hp2gv; subst; simpl in *.
    inv Hp2gv. simpl. auto.

    remember (getOperandValue (los,nts) v lc gl) as R0.
    destruct R0; try solve [inv Hp2gv].
    remember (params2GVs (los,nts) (map_list_typ_value
                (fun (typ_' : typ) (value_'' : value) => (typ_', value_''))
                tvs) lc gl) as R.
    destruct R; inv Hp2gv.
    inv Hwfvs.
    split; eauto.
      eapply getOperandValue__wf_gv; eauto.
Qed.

Lemma wf_lc_updateAddAL : forall TD f lc gv i0 t,
  wf_lc TD f lc -> 
  lookupTypViaIDFromFdef f i0 = ret t ->
  wf_genericvalue TD gv t -> 
  wf_lc TD f (updateAddAL _ lc i0 gv).
Proof.
  intros.
  intros x gvx tx Htyp Hlk.
  destruct (eq_atom_dec i0 x); subst.
    rewrite lookupAL_updateAddAL_eq in Hlk.
    inv Hlk. rewrite H0 in Htyp. inv Htyp. auto.

    rewrite <- lookupAL_updateAddAL_neq in Hlk; eauto.
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

Lemma gundef_cgv2gv__wf_gv : forall los nts gv s t
  (Hwft : wf_typ s t)
  (H0 : Constant.feasible_typ (los, nts) t)
  (HeqR : ret gv = gundef (los, nts) t),
  wf_genericvalue (los, nts) (? gv # t ?) t.
Proof.
  intros.
  eapply gundef__getTypeSizeInBits in HeqR; eauto.
  destruct HeqR as [sz1 [al1 [J1 J2]]].
  apply wf_genericvalue_intro with (sz:=sz1); auto.
    unfold getTypeSizeInBits, getTypeSizeInBits_and_Alignment,
           getTypeSizeInBits_and_Alignment_for_namedts.
    rewrite J1. auto.

    erewrite cgv2gv__getTypeSizeInBits; eauto.
Qed.

Lemma fit_gv_cgv2gv__wf_gv : forall los nts gv s t gv0
  (Hwft : wf_typ s t)
  (H0 : Constant.feasible_typ (los, nts) t)
  (HeqR : ret gv = fit_gv (los, nts) t gv0),
  wf_genericvalue (los, nts) (? gv # t ?) t.
Proof.
  intros.
  eapply fit_gv__getTypeSizeInBits in HeqR; eauto.
  destruct HeqR as [sz1 [J1 J2]].
  apply wf_genericvalue_intro with (sz:=sz1); auto.
    unfold getTypeSizeInBits, getTypeSizeInBits_and_Alignment,
           getTypeSizeInBits_and_Alignment_for_namedts in J1.
    remember (_getTypeSizeInBits_and_Alignment los
           (_getTypeSizeInBits_and_Alignment_for_namedts los (rev nts) true)
           true t) as R.
    destruct R as [[]|]; inv J1.
    erewrite cgv2gv__getTypeSizeInBits; eauto.
Qed.

Lemma initializeFrameValues__wf_lc_aux : forall los nts Ps s ifs fattr ft fid va 
  bs2 la2 la1 lc1 
  (Huniq: uniqFdef (fdef_intro (fheader_intro fattr ft fid (la1 ++ la2) va) bs2))
  (HwfF: wf_fdef ifs s (module_intro los nts Ps) 
    (fdef_intro (fheader_intro fattr ft fid (la1 ++ la2) va) bs2))
  (Hwflc: wf_lc (los,nts) 
     (fdef_intro (fheader_intro fattr ft fid (la1 ++ la2) va) bs2) lc1) 
  lc2 gvs2,
  _initializeFrameValues (los,nts) la2 gvs2 lc1 = Some lc2 -> 
  wf_lc (los,nts) (fdef_intro (fheader_intro fattr ft fid (la1 ++ la2) va) bs2) 
    lc2.
Proof.
  induction la2; simpl; intros la1 lc1 Huniq HwfF Hwflc lc2 gvs2 Hin.
    inv Hin. auto.

    destruct a. destruct p.
    destruct gvs2; simpl in *; subst.
      remember (_initializeFrameValues (los,nts) la2 nil lc1) as R1.
      destruct R1 as [lc'|]; tinv Hin.
      remember (gundef (los,nts) t) as R2.
      destruct R2; inv Hin.
        apply wf_lc_updateAddAL with (t:=t); eauto.
          rewrite_env ((la1++[(t,a,i0)])++la2).
          eapply IHla2; simpl_env; eauto.

          inv HwfF.
          simpl. 
          destruct Huniq as [Huniq1 Huniq2].
          apply NoDup_split in Huniq2.
          destruct Huniq2 as [Huniq2 _].
          rewrite NoDup_lookupTypViaIDFromArgs; auto.

          inv HwfF.
          assert (In (t, a, i0)
            (map_list_typ_attributes_id
              (fun (typ_ : typ) (attributes_ : attributes) (id_ : id) =>
              (typ_, attributes_, id_)) typ_attributes_id_list)) as J.
            rewrite <- H11.
            apply in_or_app; simpl; auto.
          apply wf_typ_list__in_args__wf_typ with (t:=t)(a:=a)(i0:=i0) in H12; 
            auto.
          apply feasible_typ_list__in_args__feasible_typ 
            with (t:=t)(a:=a)(i0:=i0) in H13; auto.
          inv H13.
          eapply gundef_cgv2gv__wf_gv; eauto.

      remember (_initializeFrameValues (los,nts) la2 gvs2 lc1) as R1.
      destruct R1 as [lc'|]; tinv Hin.
      remember (fit_gv (los,nts) t g) as R2.
      destruct R2; inv Hin.
        apply wf_lc_updateAddAL with (t:=t); eauto.
          rewrite_env ((la1++[(t,a,i0)])++la2).
          eapply IHla2; simpl_env; eauto.

          inv HwfF.
          simpl. 
          destruct Huniq as [Huniq1 Huniq2].
          apply NoDup_split in Huniq2.
          destruct Huniq2 as [Huniq2 _].
          rewrite NoDup_lookupTypViaIDFromArgs; auto.

          inv HwfF.
          assert (In (t, a, i0)
            (map_list_typ_attributes_id
              (fun (typ_ : typ) (attributes_ : attributes) (id_ : id) =>
              (typ_, attributes_, id_)) typ_attributes_id_list)) as J.
            rewrite <- H11.
            apply in_or_app; simpl; auto.
          apply wf_typ_list__in_args__wf_typ with (t:=t)(a:=a)(i0:=i0) in H12; 
            auto.
          apply feasible_typ_list__in_args__feasible_typ 
            with (t:=t)(a:=a)(i0:=i0) in H13; auto.
          inv H13.
          eapply fit_gv_cgv2gv__wf_gv; eauto.
Qed.

Lemma initializeFrameValues__wf_lc : forall ifs s los nts Ps fattr ft fid la2 va 
  bs2 lc1 
  (Huniq: uniqFdef (fdef_intro (fheader_intro fattr ft fid la2 va) bs2))
  (HwfF: wf_fdef ifs s (module_intro los nts Ps) 
    (fdef_intro (fheader_intro fattr ft fid la2 va) bs2))
  (Hwflc:wf_lc (los,nts) (fdef_intro (fheader_intro fattr ft fid la2 va) bs2) 
    lc1) 
  lc2 gvs2,
  _initializeFrameValues (los,nts) la2 gvs2 lc1 = Some lc2 -> 
  wf_lc (los,nts) (fdef_intro (fheader_intro fattr ft fid la2 va) bs2) lc2.
Proof.
  intros.  
  rewrite_env (nil++la2) in HwfF.
  rewrite_env (nil++la2) in Hwflc.
  rewrite_env (nil++la2).
  eapply initializeFrameValues__wf_lc_aux; eauto.
Qed.

Lemma initLocals__wf_lc : forall ifs s los nts Ps fattr ft fid la2 va 
  bs2
  (Huniq: uniqFdef (fdef_intro (fheader_intro fattr ft fid la2 va) bs2))
  (HwfF: wf_fdef ifs s (module_intro los nts Ps) 
    (fdef_intro (fheader_intro fattr ft fid la2 va) bs2))
  lc gvs2,
  initLocals (los,nts) la2 gvs2 = Some lc -> 
  wf_lc (los,nts) (fdef_intro (fheader_intro fattr ft fid la2 va) bs2) lc.
Proof.
  intros. unfold initLocals in H. 
  eapply initializeFrameValues__wf_lc; eauto.
    intros x gvx tx J1 J2. inv J2.
Qed.

Lemma initLocals_spec' : forall fid fa rt la va lb gvs los nts ifs s lc Ps id1 t
  (Huniq: uniqFdef (fdef_intro (fheader_intro fa rt fid la va) lb))
  (HwfF: wf_fdef ifs s (module_intro los nts Ps) 
    (fdef_intro (fheader_intro fa rt fid la va) lb))
  (Hlk: lookupTypViaIDFromFdef (fdef_intro (fheader_intro fa rt fid la va) lb)
         id1 = ret t)
  (Hinit: initLocals (los,nts) la gvs = Some lc)
  (Hin: In id1 (getArgsIDs la)),
  exists gv, lookupAL _ lc id1 = Some gv /\ wf_genericvalue (los, nts) gv t.
Proof.
  intros.
  assert (J:=Hinit).
  eapply initLocals_spec in J; eauto.
  destruct J as [gv J].
  eapply initLocals__wf_lc in Hinit; eauto.
Qed.


Lemma returnUpdateLocals__wf_lc : forall ifs los nts S F F' c Result lc lc' gl 
  lc'' Ps l1 ps1 cs1 tmn1 t B'
  (Hwfg: wf_global (los,nts) S gl) 
  (Hwfv: wf_value S (module_intro los nts Ps) F Result t),
  wf_lc (los,nts) F lc -> wf_lc (los,nts) F' lc' ->
  returnUpdateLocals (los,nts) c Result lc lc' gl = 
    ret lc'' ->
  uniqFdef F' ->
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) F' = true -> 
  In c cs1 ->
  wf_insn ifs S (module_intro los nts Ps) F' B' (insn_cmd c) ->
  wf_lc (los,nts) F' lc''.
Proof.
  intros.
  unfold returnUpdateLocals in H1.
  remember (getOperandValue (los,nts) Result lc gl) as R.
  destruct R; tinv H1.
  destruct c; inv H1; auto.
  destruct n; inv H7; auto.
  destruct t0; tinv H6.
    remember (fit_gv (los, nts) t0 g) as R.
    destruct R; inv H6.
    eapply wf_lc_updateAddAL with (t:=t0); eauto.
      eapply uniqF__lookupTypViaIDFromFdef; eauto.

      symmetry in HeqR.
      eapply getOperandValue__wf_gv in HeqR; eauto.
      inv H5. inv H20. inv H11. inv H22.
      eapply fit_gv_cgv2gv__wf_gv; eauto.
Qed.

Lemma BOP__wf_gv : forall S TD F lc gl bop0 sz0 v1 v2 gvs3,
  wf_typ S (typ_int sz0) ->
  feasible_typ TD (typ_int sz0) ->
  wf_lc TD F lc ->
  BOP TD lc gl bop0 sz0 v1 v2 = ret gvs3 ->
  wf_genericvalue TD gvs3 (typ_int sz0).
Proof.
  intros S TD F lc gl bop0 sz0 v1 v2 gvs3 Hwft Hft Hwflc Hbop.
  unfold BOP in Hbop.
  remember(getOperandValue TD v1 lc gl) as R1.
  destruct R1; tinv Hbop.
  remember(getOperandValue TD v2 lc gl) as R2.
  destruct R2; inv Hbop.
  destruct TD.
  eapply wf_genericvalue_intro; eauto.
    unfold getTypeSizeInBits. simpl. eauto.
    erewrite mbop_typsize; eauto.
Qed.

Lemma FBOP__wf_gv : forall S TD F lc gl fbop0 fp v1 v2 gvs3,
  wf_typ S (typ_floatpoint fp) ->
  feasible_typ TD (typ_floatpoint fp) ->
  wf_lc TD F lc ->
  FBOP TD lc gl fbop0 fp v1 v2 = ret gvs3 ->
  wf_genericvalue TD gvs3 (typ_floatpoint fp).
Proof.
  intros S TD F lc gl fbop0 fp v1 v2 gvs3 Hwft Hft Hwflc Hfbop.
  unfold FBOP in Hfbop.
  remember(getOperandValue TD v1 lc gl) as R1.
  destruct R1; tinv Hfbop.
  remember(getOperandValue TD v2 lc gl) as R2.
  destruct R2; inv Hfbop.
  destruct TD.
  eapply mfbop_typsize in H0; eauto.
  destruct H0 as [sz [al [J1 J2]]].
  inv Hwft; simpl in *; inv J1.
    eapply wf_genericvalue_intro; eauto.
      unfold getTypeSizeInBits. simpl. eauto.
    eapply wf_genericvalue_intro; eauto.
      unfold getTypeSizeInBits. simpl. eauto.
Qed.

Lemma extractGenericValue__wf_gv : forall S los nts t1 gv1 const_list gv typ'
  (Hwfg : wf_genericvalue (los, nts) gv1 t1)
  (HeqR3 : extractGenericValue (los, nts) t1 gv1 const_list = ret gv)
  (e0 : getSubTypFromConstIdxs const_list t1 = ret typ')
  (H0 : feasible_typ (los, nts) typ')
  (w1 : wf_typ S typ'),
  wf_genericvalue (los, nts) gv typ'.
Proof.  
  intros.
  inv Hwfg.
  inv H0.
  unfold getTypeSizeInBits in H.
  remember (getTypeSizeInBits_and_Alignment (los, nts) true t1) as R.
  destruct R as [[]|]; inv H.
  unfold getTypeSizeInBits_and_Alignment in HeqR.
  eapply extractGenericValue_typsize in e0; eauto.
  destruct e0 as [sz1 [al1 [J1 J2]]].
  eapply wf_genericvalue_intro; eauto.  
    unfold getTypeSizeInBits, getTypeSizeInBits_and_Alignment,
           getTypeSizeInBits_and_Alignment_for_namedts.
    rewrite J1. auto.
Qed.
 
Lemma insertGenericValue__wf_gv : forall los nts t1 gv1 const_list gv t2 gv2
    system5
  (Hwfg1 : wf_genericvalue (los,nts) gv1 t1)
  (Hwfg2 : wf_genericvalue (los,nts) gv2 t2)
  (H0 : feasible_typ (los, nts) t1)
  (w1 : wf_typ system5 t1)
  (HeqR3 : insertGenericValue (los, nts) t1 gv1 const_list t2 gv2 = ret gv),
  wf_genericvalue (los,nts) gv t1.
Proof.
  intros. 
  inv Hwfg1. inv Hwfg2.
  inv H0.
  unfold getTypeSizeInBits in H.
  remember (getTypeSizeInBits_and_Alignment (los, nts) true t1) as R.
  destruct R as [[]|]; inv H.
  unfold getTypeSizeInBits_and_Alignment in HeqR.
  unfold getTypeSizeInBits in H2.
  remember (getTypeSizeInBits_and_Alignment (los, nts) true t2) as R2.
  destruct R2 as [[]|]; inv H2.
  unfold getTypeSizeInBits_and_Alignment in HeqR2.
  symmetry in HeqR3.
  eapply insertGenericValue_typsize in HeqR3; eauto.
  inv HeqR3.
  eapply wf_genericvalue_intro; eauto.  
    unfold getTypeSizeInBits, getTypeSizeInBits_and_Alignment.
    rewrite <- HeqR. auto.

    rewrite <- H0. auto.
Qed.  

Lemma FCMP__wf_gv : forall F TD lc gl fcond0 fp v1 v2 gv3,
  Constant.feasible_typ TD (typ_int Size.One) ->
  wf_lc TD F lc ->
  FCMP TD lc gl fcond0 fp v1 v2 = ret gv3 ->
  wf_genericvalue TD gv3 (typ_int Size.One).
Proof.
  intros F TD lc gl fcond0 fp v1 v2 gv3 Hft Hwflc Hfcmp.
  unfold FCMP in Hfcmp.
  remember(getOperandValue TD v1 lc gl) as R1.
  destruct R1; tinv Hfcmp.
  remember(getOperandValue TD v2 lc gl) as R2.
  destruct R2; tinv Hfcmp.
  destruct TD.
  eapply mfcmp_typsize in Hfcmp; eauto.
    eapply wf_genericvalue_intro; eauto.
      unfold getTypeSizeInBits.
      simpl. auto.
    apply feasible_typ_intro; auto.
Qed.

Lemma GEP__wf_gv : forall S los nts t mp vidxs inbounds0 mp' typ' idxs gl lc
  (H0 : values2GVs (los, nts) idxs lc gl = ret vidxs)
  (H1 : GEP (los,nts) t mp vidxs inbounds0 typ' = ret mp')
  (H18 : getGEPTyp idxs t = ret typ')
  (H19 : wf_typ S typ')
  (H20 : feasible_typ (los, nts) typ'),
  wf_genericvalue (los,nts) mp' typ'.
Proof.
  intros.
  unfold GEP in H1.
  unfold getGEPTyp in H18.
  destruct idxs; tinv H18.  
  remember (getSubTypFromValueIdxs idxs t) as R4.
  destruct R4; inv H18. 
  assert(gundef (los, nts) (typ_pointer t0) = ret mp' ->
         wf_genericvalue (los, nts) mp' (typ_pointer t0)) as G.
    intro W.
    symmetry in W. inv H20. 
    eapply gundef__getTypeSizeInBits in W; eauto.
    destruct W as [sz1 [al1 [J1 J2]]].
    simpl in J1. inv J1.
    eapply wf_genericvalue_intro; simpl; try solve [
      eauto |
      unfold getTypeSizeInBits; simpl; eauto |
      simpl; auto].
  remember (GV2ptr (los, nts) (getPointerSize (los,nts)) mp) as R.
  destruct R; auto.
    remember (GVs2Nats (los, nts) vidxs) as R2.
    destruct R2; auto.
      remember (mgep (los, nts) t v0 l0) as R3.
      destruct R3; auto.
        inv H1.
        unfold ptr2GV, val2GV. simpl.
        eapply wf_genericvalue_intro; eauto.  
          unfold getTypeSizeInBits. simpl. eauto.
          simpl. auto.
Qed.

Lemma TRUNC__wf_gv : forall S F TD lc gl top0 t1 v1 t2 gv2,
  wf_typ S t2 ->
  feasible_typ TD t2 ->
  wf_lc TD F lc ->
  TRUNC TD lc gl top0 t1 v1 t2 = ret gv2 ->
  wf_genericvalue TD gv2 t2.
Proof.
  intros S F TD lc gl top0 t1 v1 t2 gv2 Hwft Hft Hwflc Htop.
  unfold TRUNC in Htop.
  remember(getOperandValue TD v1 lc gl) as R1.
  destruct R1; tinv Htop.
  destruct TD. inv Hft.
  eapply mtrunc_typsize in Htop; eauto.
  destruct Htop as [sz [al [J1 J2]]].
  eapply wf_genericvalue_intro; eauto.
    unfold getTypeSizeInBits, getTypeSizeInBits_and_Alignment. 
    unfold getTypeSizeInBits_and_Alignment_for_namedts in *.
    rewrite J1. eauto.
Qed.

Lemma EXT__wf_gv : forall S F TD lc gl eop0 t1 v1 t2 gv2,
  wf_typ S t2 ->
  feasible_typ TD t2 ->
  wf_lc TD F lc ->
  EXT TD lc gl eop0 t1 v1 t2 = ret gv2 ->
  wf_genericvalue TD gv2 t2.
Proof.
  intros S F TD lc gl eop0 t1 v1 t2 gv2 Hwft Hft Hwflc Heop.
  unfold EXT in Heop.
  remember(getOperandValue TD v1 lc gl) as R1.
  destruct R1; tinv Heop.
  destruct TD. inv Hft.
  eapply mext_typsize in Heop; eauto.
  destruct Heop as [sz [al [J1 J2]]].
  eapply wf_genericvalue_intro; eauto.
    unfold getTypeSizeInBits, getTypeSizeInBits_and_Alignment. 
    unfold getTypeSizeInBits_and_Alignment_for_namedts in *.
    rewrite J1. eauto.
Qed.


Lemma CAST__wf_gv : forall S F los nts lc gl cop0 t1 v1 t2 gv2 id0 B Ps
  (Hwfg : wf_global (los, nts) S gl)
  (Hwflc : wf_lc (los, nts) F lc)
  (H6 : wf_cast nil S (module_intro los nts Ps) F B
         (insn_cmd (insn_cast id0 cop0 t1 v1 t2)))
  (H : CAST (los, nts) lc gl cop0 t1 v1 t2 = ret gv2),
  wf_genericvalue (los, nts) gv2 t2.
Proof.
  intros.
  unfold CAST in H.
  remember(getOperandValue (los,nts) v1 lc gl) as R1.
  destruct R1; tinv H.
  symmetry in HeqR1.
  unfold mcast in H.
  symmetry in H.
  inv H6.
    inv H15.
    eapply getOperandValue__wf_gv in HeqR1; eauto.
    eapply gundef__getTypeSizeInBits in H; eauto.
    destruct H as [sz0 [al0 [J1 J2]]].
    eapply wf_genericvalue_intro; eauto.
      unfold getTypeSizeInBits, getTypeSizeInBits_and_Alignment,
             getTypeSizeInBits_and_Alignment_for_namedts.
      rewrite J1. auto.

    inv H15.
    eapply gundef__getTypeSizeInBits with (s:=S) in H; eauto.
    destruct H as [sz0 [al0 [J1 J2]]].
    eapply wf_genericvalue_intro; eauto.
      unfold getTypeSizeInBits, getTypeSizeInBits_and_Alignment,
             getTypeSizeInBits_and_Alignment_for_namedts.
      rewrite J1. auto.
       
    eapply getOperandValue__wf_gv in HeqR1; eauto.
    unfold mbitcast in H. inv H.
    inv HeqR1.
    eapply wf_genericvalue_intro; eauto.
Qed.    

Lemma ICMP__wf_gv : forall F TD lc gl cond0 t v1 v2 gv2,
  Constant.feasible_typ TD (typ_int Size.One) ->
  wf_lc TD F lc ->
  ICMP TD lc gl cond0 t v1 v2 = ret gv2 ->
  wf_genericvalue TD gv2 (typ_int Size.One).
Proof.
  intros F TD lc gl cond0 t v1 v2 gv2 Hft Hwflc Hicmp.
  unfold ICMP in Hicmp.
  remember(getOperandValue TD v1 lc gl) as R1.
  destruct R1; tinv Hicmp.
  remember(getOperandValue TD v2 lc gl) as R2.
  destruct R2; tinv Hicmp.
  destruct TD.
  eapply micmp_typsize in Hicmp; eauto.
    eapply wf_genericvalue_intro; eauto.
      unfold getTypeSizeInBits.
      simpl. auto.
    apply feasible_typ_intro; auto.
Qed.

Lemma in_middle : forall A (c:A) cs1 cs2, In c (cs1 ++ c :: cs2).
Proof.
  intros.
  apply in_app_iff; simpl; auto.
Qed.

(*********************************************)
(** * Preservation *)

Lemma preservation_dbCall_case : forall fid l' fa rt la va lb bs_contents gvs los
  nts ifs s lc Ps
  (bs_bound : incl bs_contents (bound_blocks lb))
  (H0 : incl bs_contents [l']) 
  (Huniq: uniqFdef (fdef_intro (fheader_intro fa rt fid la va) lb))
  (HwfF: wf_fdef ifs s (module_intro los nts Ps) 
    (fdef_intro (fheader_intro fa rt fid la va) lb))
  (Hinit : initLocals (los,nts) la gvs = Some lc),
   match
     fold_left
       (inscope_of_block (fdef_intro (fheader_intro fa rt fid la va) lb) l')
       bs_contents (ret getArgsIDs la)
   with
   | ret ids0 =>
       wf_defs (los,nts) (fdef_intro (fheader_intro fa rt fid la va) lb) lc ids0
   | merror => False
   end.
Proof.
  intros.
  assert (J:=bs_bound).
  apply fold_left__bound_blocks with (t:=rt)(i0:=fid)(la:=la)(va:=va)(fa:=fa)
    (l0:=l')(init:=getArgsIDs la) in J.
  destruct J as [r J].
  rewrite J.       
  apply fold_left__spec in J.
  destruct J as [_ [_ J]].
  apply wf_defs_intro.
  intros id1 Hin.
  apply J in Hin.
  destruct Hin as [Hin | Hin].    
    assert (J1:=Hin).
    apply InArgsIDs_lookupTypViaIDFromFdef with (t0:=rt)(id0:=fid)(la0:=la)
      (va0:=va)(bs:=lb)(fa:=fa) in J1.
    destruct J1 as [t J1].
    exists t. rewrite J1.
    eapply initLocals_spec' in Hinit; eauto.
    destruct Hinit as [gv Hinit].
    exists gv. split; auto.
  
    destruct Hin as [b1 [l1 [Hin _]]].
    clear - H0 Hin.
    assert (J:=Hin).
    apply ListSet.set_diff_elim1 in Hin.
    apply ListSet.set_diff_elim2 in J.
    apply H0 in Hin.
    simpl in Hin. 
    destruct Hin as [Hin | Hin]; subst; try inversion Hin.
    simpl in J. contradict J; auto.
Qed.

Definition wf_ExecutionContext TD (ps:list product) (ec:ExecutionContext) 
  : Prop :=
let '(mkEC f b cs tmn lc als) := ec in
isReachableFromEntry f b /\
blockInFdefB b f = true /\
InProductsB (product_fdef f) ps = true /\
wf_lc TD f lc /\
match cs with
| nil => 
    match inscope_of_tmn f b tmn with
    | Some ids => wf_defs TD f lc ids
    | None => False
    end
| c::_ =>
    match inscope_of_cmd f b c with
    | Some ids => wf_defs TD f lc ids
    | None => False
    end
end /\
exists l1, exists ps, exists cs',
b = block_intro l1 ps (cs'++cs) tmn.

Definition wf_call (ec:ExecutionContext) (ecs:ECStack) : Prop :=
let '(mkEC f _ _ _ _ _) := ec in
forall b, blockInFdefB b f ->
let '(block_intro _ _ _ tmn) := b in
match tmn with
| insn_return _ _ _ | insn_return_void _ =>
    match ecs with
    | nil => True
    | mkEC f' b' (insn_call _ _ _ _ _ _ ::_) tmn' lc' als'::ecs' => True
    | _ => False
    end
| _ => True
end.

Fixpoint wf_ECStack TD (ps:list product) (ecs:ECStack) : Prop :=
match ecs with
| nil => False
| ec::ecs' => 
    wf_ExecutionContext TD ps ec /\ wf_ECStack TD ps ecs' /\ wf_call ec ecs'
end.

Definition wf_State (S:State) : Prop :=
let '(mkState s (los, nts) ps ecs gl _ _) := S in
wf_global (los, nts) s gl /\
wf_system nil s /\
moduleInSystemB (module_intro los nts ps) s = true /\
wf_ECStack (los, nts) ps ecs.

Lemma wf_State__inv : forall S los nts Ps F B c cs tmn lc als EC gl fs Mem0,
  wf_State (mkState S (los,nts) Ps
              ((mkEC F B (c::cs) tmn lc als)::EC) gl fs Mem0) ->
  wf_global (los, nts) S gl /\
  wf_lc (los,nts) F lc /\ 
  wf_insn nil S (module_intro los nts Ps) F B (insn_cmd c).
Proof.
  intros.
  destruct H as 
    [Hwfg [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]] 
     [HwfEC HwfCall]]]]
    ]; subst.
  split; auto. 
  split; auto. 
    eapply wf_system__wf_cmd; eauto using in_middle.
Qed.  

Lemma preservation_cmd_updated_case : forall
  (S : system)
  (los : layouts)
  (nts : namedts)
  (Ps : list product)
  (F : fdef)
  (B : block)
  (lc : GVMap)
  (gl : GVMap)
  (fs : GVMap)
  (gv3 : GenericValue)
  (EC : list ExecutionContext)
  (cs : list cmd)
  (tmn : terminator)
  (Mem0 : mem)
  (als : list mblock)
  id0 c0
  (Hid : Some id0 = getCmdID c0)
  t0
  (Htyp : Some t0 = getCmdTyp c0)
  (Hwfgv : wf_genericvalue (los,nts) gv3 t0)
  (HwfS1 : wf_State
            {|
            CurSystem := S;
            CurTargetData := (los, nts);
            CurProducts := Ps;
            ECS := {|
                   CurFunction := F;
                   CurBB := B;
                   CurCmds := c0 :: cs;
                   Terminator := tmn;
                   Locals := lc;
                   Allocas := als |} :: EC;
            Globals := gl;
            FunTable := fs;
            Mem := Mem0 |}),
   wf_State
     {|
     CurSystem := S;
     CurTargetData := (los, nts);
     CurProducts := Ps;
     ECS := {|
            CurFunction := F;
            CurBB := B;
            CurCmds := cs;
            Terminator := tmn;
            Locals := updateAddAL GenericValue lc id0 gv3;
            Allocas := als |} :: EC;
     Globals := gl;
     FunTable := fs;
     Mem := Mem0 |}.
Proof.
  intros.
  destruct HwfS1 as 
    [Hwfg [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]]
     [HwfEC HwfCall]]]]
    ]; subst.
  remember (inscope_of_cmd F (block_intro l3 ps3 (cs3' ++ c0 :: cs) tmn) c0) 
    as R1. 
  assert (uniqFdef F) as HuniqF.
    eapply wf_system__uniqFdef; eauto.
  destruct R1; try solve [inversion Hinscope1].
  repeat (split; try solve [auto]).
      Case "wflc".
      eapply wf_lc_updateAddAL; eauto.
        eapply uniqF__lookupTypViaIDFromFdef; eauto using in_middle.

      assert (Hid':=Hid).
      symmetry in Hid.
      apply getCmdLoc_getCmdID in Hid.
       subst.
      destruct cs; simpl_env in *.
      Case "1.1.1".
        assert (~ In (getCmdLoc c0) (getCmdsLocs cs3')) as Hnotin.
          eapply wf_system__uniq_block with (f:=F) in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _].
          rewrite getCmdsLocs_app in J.
          simpl in J.
          apply NoDup_last_inv in J. auto.

        apply inscope_of_cmd_tmn in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].        
        rewrite <- J1.
        assert (In c0 (cs3' ++ [c0])) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc; 
          eauto.
        rewrite <- Hid' in J2.
        eapply wf_defs_updateAddAL with (t1:=t0) ; eauto.
          eapply uniqF__lookupTypViaIDFromFdef; eauto.
        
      Case "1.1.2".
        assert (NoDup (getCmdsLocs (cs3' ++ [c0] ++ [c] ++ cs))) as Hnodup.
          eapply wf_system__uniq_block with (f:=F) in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _]. auto.
        apply inscope_of_cmd_cmd in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].        
        rewrite <- J1.
        assert (In c0 (cs3' ++ [c0] ++ [c] ++ cs)) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc; 
          eauto.
        rewrite <- Hid' in J2.
        eapply wf_defs_updateAddAL with (t1:=t0) ; eauto.
          eapply uniqF__lookupTypViaIDFromFdef; eauto.

  exists l3. exists ps3. exists (cs3'++[c0]). simpl_env. auto.
Qed.

Lemma preservation_cmd_non_updated_case : forall
  (S : system)
  (los : layouts)
  (nts : namedts)
  (Ps : list product)
  (F : fdef)
  (B : block)
  (lc : GVMap)
  (gl : GVMap)
  (fs : GVMap)
  (EC : list ExecutionContext)
  (cs : list cmd)
  (tmn : terminator)
  (Mem0 : mem)
  (als : list mblock)
  c0
  (Hid : getCmdID c0 = None)
  (HwfS1 : wf_State
            {|
            CurSystem := S;
            CurTargetData := (los, nts);
            CurProducts := Ps;
            ECS := {|
                   CurFunction := F;
                   CurBB := B;
                   CurCmds := c0 :: cs;
                   Terminator := tmn;
                   Locals := lc;
                   Allocas := als |} :: EC;
            Globals := gl;
            FunTable := fs;
            Mem := Mem0 |}),
   wf_State
     {|
     CurSystem := S;
     CurTargetData := (los, nts);
     CurProducts := Ps;
     ECS := {|
            CurFunction := F;
            CurBB := B;
            CurCmds := cs;
            Terminator := tmn;
            Locals := lc;
            Allocas := als |} :: EC;
     Globals := gl;
     FunTable := fs;
     Mem := Mem0 |}.
Proof.
  intros.
  destruct HwfS1 as 
    [Hwfg [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]]
     [HwfEC HwfCall]]]]
    ]; subst.
  remember (inscope_of_cmd F (block_intro l3 ps3 (cs3' ++ c0 :: cs) tmn) c0) 
    as R1. 
  destruct R1; try solve [inversion Hinscope1].
  repeat (split; try solve [auto]).
      destruct cs; simpl_env in *.
      Case "1.1.1".
        assert (~ In (getCmdLoc c0) (getCmdsLocs cs3')) as Hnotin.
          eapply wf_system__uniq_block with (f:=F) in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _].
          rewrite getCmdsLocs_app in J.
          simpl in J.
          apply NoDup_last_inv in J. auto.

        apply inscope_of_cmd_tmn in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].        
        rewrite <- J1.
        assert (In c0 (cs3' ++ [c0])) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc; 
          eauto.
        rewrite Hid in J2.
        eapply wf_defs_eq; eauto.
        
      Case "1.1.2".
        assert (NoDup (getCmdsLocs (cs3' ++ [c0] ++ [c] ++ cs))) as Hnodup.
          eapply wf_system__uniq_block with (f:=F) in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _]. auto.
        apply inscope_of_cmd_cmd in HeqR1; auto.
        destruct HeqR1 as [ids2 [J1 J2]].        
        rewrite <- J1.
        assert (In c0 (cs3' ++ [c0] ++ [c] ++ cs)) as HinCs.
          apply in_or_app. right. simpl. auto.
        assert (Hwfc := HBinF1).
        eapply wf_system__wf_cmd with (c:=c0) in Hwfc; 
          eauto.
        rewrite Hid in J2.
        eapply wf_defs_eq ; eauto.

  exists l3. exists ps3. exists (cs3'++[c0]). simpl_env. auto.
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

Lemma preservation : forall S1 S2 tr,
  dsInsn S1 S2 tr -> wf_State S1 -> wf_State S2.
Proof.
  intros S1 S2 tr HdsInsn HwfS1.
  (dsInsn_cases (induction HdsInsn) Case); destruct TD as [los nts].
Focus.
Case "dsReturn".
  destruct HwfS1 as 
    [Hwfg [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l1 [ps1 [cs1' Heq1]]]]]]]]
     [
       [
         [Hreach2 [HBinF2 [HFinPs2 [Hwflc2 [Hinscope2 [l2 [ps2 [cs2' Heq2]]]]]]]]
         [HwfEC HwfCall]
       ]
       HwfCall'
     ]
    ]]]]; subst.
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
    split; auto.
    split; auto.

    remember (getCmdID c') as R.
    destruct c'; try solve [inversion H].
    assert (In (insn_call i0 n c t v p) 
      (cs2'++[insn_call i0 n c t v p] ++ cs')) as HinCs.
      apply in_or_app. right. simpl. auto.
    assert (Hwfc := HBinF2).
    eapply wf_system__wf_cmd with (c:=insn_call i0 n c t v p) in Hwfc; eauto.
    assert (uniqFdef F') as HuniqF.
      eapply wf_system__uniqFdef; eauto.

    split.
      eapply wf_system__wf_tmn in HBinF1; eauto.
      inv HBinF1.
      eapply returnUpdateLocals__wf_lc with (Result:=Result)(lc:=lc); eauto.
    split.
    SSCase "1.1".
      destruct cs'; simpl_env in *.
      SSSCase "1.1.1".
        assert (~ In (getCmdLoc (insn_call i0 n c t v p)) (getCmdsLocs cs2')) 
          as Hnotin.
          eapply wf_system__uniq_block with (f:=F') in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _].
          rewrite getCmdsLocs_app in J.
          simpl in J.
          apply NoDup_last_inv in J. auto.
        apply inscope_of_cmd_tmn in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].        
        rewrite <- J1.
        unfold returnUpdateLocals in H1. simpl in H1.
        remember (getOperandValue (los,nts) Result lc gl) as R1.
        destruct R1; try solve [inv H1].
        destruct R.
          destruct n; inv HeqR. 
          destruct t; tinv H1.
          remember (fit_gv (los, nts) t g) as R1.
          destruct R1; inv H1.
          inv Hwfc. inv H16. inv H7. inv H18.
          eapply wf_defs_updateAddAL with (t1:=typ1) ; eauto.
            eapply uniqF__lookupTypViaIDFromFdef; eauto.
            eapply fit_gv_cgv2gv__wf_gv; eauto.

          destruct n; inv HeqR. inv H1.
          simpl in J2.
          eapply wf_defs_eq; eauto. 
        
      SSSCase "1.1.2".
        assert (NoDup (getCmdsLocs (cs2' ++ [insn_call i0 n c t v p] ++ [c0] ++ 
          cs'))) as Hnodup.
          eapply wf_system__uniq_block with (f:=F') in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _]. auto.
        apply inscope_of_cmd_cmd in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].        
        rewrite <- J1.
        unfold returnUpdateLocals in H1. simpl in H1.
        remember (getOperandValue (los,nts) Result lc gl) as R1.
        destruct R1; try solve [inv H1].
        destruct R.
          destruct n; inv HeqR. 
          destruct t; tinv H1.
          remember (fit_gv (los, nts) t g) as R1.
          destruct R1; inv H1.
          inv Hwfc. inv H16. inv H7. inv H18.
          eapply wf_defs_updateAddAL with (t1:=typ1) ; eauto.
            eapply uniqF__lookupTypViaIDFromFdef; eauto.
            eapply fit_gv_cgv2gv__wf_gv; eauto.

          destruct n; inv HeqR. inv H1.
          simpl in J2.
          eapply wf_defs_eq; eauto. 
    SSCase "1.2".
      exists l2. exists ps2. exists (cs2'++[insn_call i0 n c t v p]).   
      simpl_env. auto.
Unfocus.

Focus.
Case "dsReturnVoid".
  destruct HwfS1 as 
    [Hwfg [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l1 [ps1 [cs1' Heq1]]]]]]]] 
     [
       [
         [Hreach2 [HBinF2 [HFinPs2 [Hwflc2 [Hinscope2 [l2 [ps2 [cs2' Heq2]]]]]]]]
         [HwfEC HwfCall]
       ]
       HwfCall'
     ]
    ]]]]; subst.
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
    split; auto.
    split; auto.
    split; auto.
    split.   
    SSCase "1.1".
      apply HwfCall' in HBinF1. simpl in HBinF1.
      destruct cs'; simpl_env in *.
      SSSCase "1.1.1".
        assert (~ In (getCmdLoc c') (getCmdsLocs cs2')) as Hnotin.
          eapply wf_system__uniq_block with (f:=F') in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _].
          rewrite getCmdsLocs_app in J.
          simpl in J.
          apply NoDup_last_inv in J. auto.
        clear - HeqR2 Hinscope2 H HwfCall' HBinF1 Hnotin H1.
        apply inscope_of_cmd_tmn in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].        
        rewrite <- J1.
        remember (getCmdID c') as R.
        destruct c'; try solve [inversion H].
        destruct n; inversion H1.
        simpl in HeqR. subst R.
        eapply wf_defs_eq; eauto. 
        
      SSSCase "1.1.2".
        assert (NoDup (getCmdsLocs (cs2' ++ [c'] ++ [c] ++ cs'))) as Hnodup.
          eapply wf_system__uniq_block with (f:=F') in HwfSystem; eauto.        
          simpl in HwfSystem.
          apply NoDup_inv in HwfSystem.
          destruct HwfSystem as [_ J].
          apply NoDup_inv in J.
          destruct J as [J _]. auto.
        clear - HeqR2 Hinscope2 H HwfCall' HBinF1 Hnodup H1.
        apply inscope_of_cmd_cmd in HeqR2; auto.
        destruct HeqR2 as [ids2 [J1 J2]].        
        rewrite <- J1.
        remember (getCmdID c') as R.
        destruct c'; try solve [inversion H].
        destruct n; inversion H1.
        simpl in HeqR. subst R.
        eapply wf_defs_eq; eauto. 

    SSCase "1.2".
      exists l2. exists ps2. exists (cs2'++[c']).   
      simpl_env. auto.
Unfocus.

Focus.
Case "dsBranch".
  destruct HwfS1 as 
    [Hwfg [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]]
     [HwfEC HwfCall]]]]
    ]; subst.
  remember (inscope_of_tmn F
             (block_intro l3 ps3 (cs3' ++ nil)(insn_br bid Cond l1 l2))
             (insn_br bid Cond l1 l2)) as R1. 
  destruct R1; try solve [inversion Hinscope1].
  split; auto.
  split; auto.
  split; auto.
  split; auto.
  SCase "1".
    assert (HwfF := HwfSystem).
    eapply wf_system__wf_fdef with (f:=F) in HwfF; eauto.
    assert (HuniqF := HwfSystem).
    eapply wf_system__uniqFdef with (f:=F) in HuniqF; eauto.
    split.
      clear - Hreach1 H0 HBinF1 HFinPs1 HmInS HwfSystem HuniqF.
      unfold isReachableFromEntry in *.
      destruct (isGVZero (los, nts) c).
        symmetry in H0.
        apply lookupBlockViaLabelFromFdef_inv in H0; eauto.
        destruct H0 as [H0 _].
        eapply reachable_successors; eauto.
          simpl. auto.
      
        symmetry in H0.
        apply lookupBlockViaLabelFromFdef_inv in H0; eauto.
        destruct H0 as [H0 _].
        eapply reachable_successors; eauto.
          simpl. auto.
    split. 
      clear - H0 HBinF1 HFinPs1 HmInS HwfSystem HuniqF.
      destruct (isGVZero (los, nts) c).
        symmetry in H0.
        apply lookupBlockViaLabelFromFdef_inv in H0; auto.
          destruct H0; auto.
        symmetry in H0.
        apply lookupBlockViaLabelFromFdef_inv in H0; auto.
          destruct H0; auto.
    split; auto.
    split. 
      destruct (isGVZero (los, nts) c);
        eapply wf_lc_br_aux in H1; eauto.
    split.
      clear - H0 HeqR1 H1 Hinscope1 H HwfSystem HBinF1 HwfF HuniqF Hwflc1 Hwfg.
      eapply inscope_of_tmn_br in HeqR1; eauto.
      destruct HeqR1 as [ids0' [HeqR1 [J1 J2]]].
      destruct cs'; rewrite <- HeqR1; auto.

      exists l'. exists ps'. exists nil. simpl_env. auto.
Unfocus.

Focus.
Case "dsBranch_uncond".
  destruct HwfS1 as 
    [Hwfg [HwfSystem [HmInS [
     [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]] 
     [HwfEC HwfCall]]]]
    ]; subst.
  remember (inscope_of_tmn F
             (block_intro l3 ps3 (cs3' ++ nil)(insn_br_uncond bid l0))
             (insn_br_uncond bid l0)) as R1. 
  destruct R1; try solve [inversion Hinscope1].
  split; auto.
  split; auto.
  split; auto.
  SCase "1".
    split; auto.
    assert (HwfF := HwfSystem).
    eapply wf_system__wf_fdef with (f:=F) in HwfF; eauto.
    assert (HuniqF := HwfSystem).
    eapply wf_system__uniqFdef with (f:=F) in HuniqF; eauto.
    split.
      clear - Hreach1 H HBinF1 HFinPs1 HmInS HwfSystem HuniqF.
      unfold isReachableFromEntry in *.
      symmetry in H.
      apply lookupBlockViaLabelFromFdef_inv in H; auto.
      destruct H as [H _].
      eapply reachable_successors; eauto.
        simpl. auto.
    split.
      clear - H HBinF1 HFinPs1 HmInS HwfSystem HuniqF.
      symmetry in H.
      apply lookupBlockViaLabelFromFdef_inv in H; auto.
        destruct H; auto.
    split; auto.
    split. eapply wf_lc_br_aux in H0; eauto.
    split.
      clear - H0 HeqR1 Hinscope1 H HwfSystem HBinF1 HwfF HuniqF Hwfg Hwflc1.
      assert (Hwds := HeqR1).
      eapply inscope_of_tmn_br_uncond with (cs':=cs')(l':=l')(ps':=ps')
        (tmn':=tmn') in HeqR1; eauto.
      destruct HeqR1 as [ids0' [HeqR1 [J1 J2]]].
      destruct cs'; rewrite <- HeqR1; auto.

      exists l'. exists ps'. exists nil. simpl_env. auto.
Unfocus.

Case "dsBop". eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  apply wf_State__inv in HwfS1.
  destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
  inv Hwfc.
  apply wf_value__wf_typ in H8.
  destruct H8 as [J1 J2].
  eapply BOP__wf_gv; eauto.

Case "dsFBop". eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  apply wf_State__inv in HwfS1.
  destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
  inv Hwfc.
  apply wf_value__wf_typ in H8.
  destruct H8 as [J1 J2].
  eapply FBOP__wf_gv; eauto.

Case "dsExtractValue".
  assert (J':=HwfS1).
  destruct J' as 
      [Hwfg [HwfSystem [HmInS [
        [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]] 
        [HwfEC HwfCall]]]]
      ]; subst.
  assert (exists t0, getSubTypFromConstIdxs idxs t = Some t0) as J.
    eapply wf_system__wf_cmd with (c:=insn_extractvalue id0 t v idxs) in HBinF1; 
      eauto.
      inv HBinF1.
      destruct H15 as [idxs0 [o [J1 J2]]].
      symmetry in J2.
      eapply mgetoffset__getSubTypFromConstIdxs in J2; eauto.

      apply in_or_app; simpl; auto.
  destruct J as [t0 J].
  eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
    eapply wf_system__wf_cmd in HBinF1; eauto using in_middle.
    inv HBinF1. 
    destruct H15 as [idxs0 [o [J1 J2]]].
    symmetry in J2.
    eapply getSubTypFromConstIdxs__mgetoffset in J2; eauto.
    subst.
    eapply getOperandValue__wf_gv in H; eauto.
    eapply extractGenericValue__wf_gv with (t1:=t); eauto.

Case "dsInsertValue". 
  eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
    apply wf_State__inv in HwfS1.
    destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
    inv Hwfc.
    eapply getOperandValue__wf_gv in H; eauto.
    eapply getOperandValue__wf_gv in H0; eauto.
    apply wf_value__wf_typ in H13. destruct H13.
    eapply insertGenericValue__wf_gv; eauto.

Case "dsMalloc". eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  unfold blk2GV, ptr2GV, val2GV. simpl.
  eapply wf_genericvalue_intro; eauto.  
    unfold getTypeSizeInBits. simpl. eauto.
    simpl. auto.
  
Case "dsFree". eapply preservation_cmd_non_updated_case in HwfS1; eauto.
Case "dsAlloca". eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  unfold blk2GV, ptr2GV, val2GV. simpl.
  eapply wf_genericvalue_intro; eauto.  
    unfold getTypeSizeInBits. simpl. eauto.
    simpl. auto.

Case "dsLoad".  eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  apply wf_State__inv in HwfS1.
  destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
  inv Hwfc.
  apply wf_value__wf_typ in H9. destruct H9.
  inv H1. inv H2. inv H13.
  eapply mload__getTypeSizeInBits in H0; eauto.
    destruct H0 as [sz [J1 J2]]. 
    eapply wf_genericvalue_intro; eauto.  

Case "dsStore". eapply preservation_cmd_non_updated_case in HwfS1; eauto.
Case "dsGEP". 
  assert (J:=HwfS1).
  destruct J as 
    [Hwfg [HwfSystem [HmInS [
         [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]]
         [HwfEC HwfCall]]]]
    ]; subst.
  eapply wf_system__wf_cmd with (c:=insn_gep id0 inbounds0 t v idxs) in HBinF1;
    eauto using in_middle.
  inv HBinF1; eauto.
  eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
    rewrite H1 in H19. inv H19.
    eapply GEP__wf_gv; eauto.

Case "dsTrunc". eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  apply wf_State__inv in HwfS1.
  destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
  inv Hwfc. 
  inv H6; eapply TRUNC__wf_gv with (S:=S); eauto.

Case "dsExt". eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  apply wf_State__inv in HwfS1.
  destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
  inv Hwfc. 
  inv H6; eapply EXT__wf_gv with (S:=S); eauto.

Case "dsCast". eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  apply wf_State__inv in HwfS1.
  destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
  inv Hwfc. 
  eapply CAST__wf_gv in H6; eauto.

Case "dsIcmp". eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  apply wf_State__inv in HwfS1.
  destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
  inv Hwfc. 
  eapply ICMP__wf_gv in H; eauto.

Case "dsFcmp". eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.
  apply wf_State__inv in HwfS1.
  destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
  inv Hwfc. 
  eapply FCMP__wf_gv in H; eauto.

Case "dsSelect".
  assert (J:=HwfS1).
  apply wf_State__inv in J.
  destruct J as [Hwfg [Hwflc Hwfc]].
  inv Hwfc. 
  eapply getOperandValue__wf_gv in H0; eauto.
  eapply getOperandValue__wf_gv in H1; eauto.
  destruct (isGVZero (los, nts) c); 
    eapply preservation_cmd_updated_case in HwfS1; simpl; eauto.

Focus.
Case "dsCall".
  destruct HwfS1 as [Hwfg [HwfSys [HmInS [
    [Hreach [HBinF [HFinPs [Hwflc [Hinscope [l1 [ps [cs'' Heq]]]]]]]]
    [HwfECs HwfCall]]]]]; subst.
  assert (InProductsB (product_fdef (fdef_intro 
    (fheader_intro fa rt fid la va) lb)) Ps = true) as HFinPs'.
    eapply lookupFdefViaGV_inv; eauto.
  split; auto.
  split; auto.
  split; auto.
  split.
  SCase "1".     
    assert (uniqFdef (fdef_intro (fheader_intro fa rt fid la va) lb)) as Huniq.
      eapply wf_system__uniqFdef; eauto.
    assert (wf_fdef nil S (module_intro los nts Ps) 
      (fdef_intro (fheader_intro fa rt fid la va) lb)) as HwfF.
      eapply wf_system__wf_fdef; eauto.

    split.
      simpl. eapply reachable_entrypoint; eauto.
    split.
     apply entryBlockInFdef in H0; auto.
    split; auto.
    split.
     eapply initLocals__wf_lc; eauto.
    split.
     assert (ps'=nil) as EQ.
       eapply entryBlock_has_no_phinodes with (ifs:=nil)(s:=S); eauto.        
     subst.
     apply dom_entrypoint in H0.
     destruct cs'.
       unfold inscope_of_tmn.
       remember ((dom_analyze (fdef_intro (fheader_intro fa rt fid la va) lb)) 
         !! l') as R.
       destruct R.
       eapply preservation_dbCall_case; eauto.

       unfold inscope_of_cmd.
       remember ((dom_analyze (fdef_intro (fheader_intro fa rt fid la va) lb)) 
         !! l') as R.
       destruct R. simpl.
       destruct (eq_atom_dec (getCmdLoc c) (getCmdLoc c)) as [|n]; 
         try solve [contradict n; auto]. 
       eapply preservation_dbCall_case; eauto.

    exists l'. exists ps'. exists nil. simpl_env. auto.
  split.
  SCase "2".
    repeat (split; auto). eauto.
  SCase "3".
    simpl. intros b HbInBs. destruct b.
    destruct t; auto.

Unfocus.

Case "dsExCall". 
  unfold exCallUpdateLocals in H2.
  destruct noret0.
    inv H2.
    eapply preservation_cmd_non_updated_case in HwfS1; eauto.

    assert (exists t0, getCmdTyp (insn_call rid false ca ft fv lp) = Some t0)
      as J.
      destruct HwfS1 as 
       [Hwfg [HwfSystem [HmInS [
         [Hreach1 [HBinF1 [HFinPs1 [Hwflc1 [Hinscope1 [l3 [ps3 [cs3' Heq1]]]]]]]]
         [HwfEC HwfCall]]]]
       ]; subst.
       eapply wf_system__wf_cmd with (c:=insn_call rid false ca ft fv lp) 
        in HBinF1; eauto.
      simpl.
      inv HBinF1; eauto. 
      apply in_or_app; simpl; auto.
    destruct J as [t0 J].
    destruct oresult; tinv H2.
    destruct ft; tinv H2.
    remember (fit_gv (los, nts) ft g) as R.
    destruct R; inv H2.
    eapply preservation_cmd_updated_case with (t0:=t0) in HwfS1; simpl; eauto.
      inv J.
      apply wf_State__inv in HwfS1.
      destruct HwfS1 as [Hwfg [Hwflc Hwfc]].
      inv Hwfc. inv H17. inv H8. inv H19.
      eapply fit_gv_cgv2gv__wf_gv; eauto.
Qed.

(*********************************************)
(** * Progress *)

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
                      (fun const_ : const => 
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
                      (fun (const_ : const) (typ_ : typ) => 
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
  unfold extractGenericValue.
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
  unfold insertGenericValue.
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

Lemma const2GV_isnt_stuck : forall TD S gl c t,
  wf_const S TD c t ->
  feasible_typ TD t ->
  wf_global TD S gl ->
  exists gv, const2GV TD gl c = Some gv.
Proof.
  intros.
  destruct const2GV_isnt_stuck_mutind as [J _].
  unfold const2GV_isnt_stuck_Prop in J.
  unfold const2GV.
  inv H0.
  eapply J in H; eauto.
  destruct H as [gv H].
  rewrite H. eauto.
Qed.

Lemma state_tmn_typing : forall TD ifs s m f l1 ps1 cs1 tmn1 defs id1 lc,
  isReachableFromEntry f (block_intro l1 ps1 cs1 tmn1) ->
  wf_insn ifs s m f (block_intro l1 ps1 cs1 tmn1) (insn_terminator tmn1) ->
  Some defs = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn1) tmn1 ->
  wf_defs TD f lc defs ->
  uniqFdef f ->
  In id1 (getInsnOperands (insn_terminator tmn1)) ->
  exists t, exists gv, 
    lookupTypViaIDFromFdef f id1 = munit t /\
    lookupAL _ lc id1 = Some gv /\ wf_genericvalue TD gv t.
Proof.
  intros TD ifs s m f l1 ps1 cs1 tmn1 defs id1 lc Hreach HwfInstr Hinscope 
    HwfDefs HuniqF HinOps.
  apply wf_insn__wf_insn_base in HwfInstr; 
    try solve [unfold isPhiNode; simpl; auto].
  inv HwfInstr.  
 
  assert (
     In (f, block_intro l1 ps1 cs1 tmn1, insn_terminator tmn1, id1)
     (unmake_list_fdef_block_insn_id
        (make_list_fdef_block_insn_id
           (map_list_id
              (fun id_ : id =>
               (f, block_intro l1 ps1 cs1 tmn1, insn_terminator tmn1, id_))
              id_list)))
    ) as G.
    rewrite H5 in HinOps. clear - HinOps.
    induction id_list; simpl in *; auto.
      destruct HinOps as [HinOps | HinOps]; subst; auto.

  apply wf_operand_list__elim with (f1:=f)(b1:=block_intro l1 ps1 cs1 tmn1)
    (insn1:=insn_terminator tmn1)(id1:=id1) in H6; auto.

  inv H6.
  clear - H11 HwfDefs Hinscope H0 Hreach H9 HuniqF.
  eapply wf_defs_elim; eauto.
    unfold inscope_of_tmn in Hinscope.
    destruct f. destruct f.
    remember ((dom_analyze (fdef_intro (fheader_intro f t i0 a v) b)) !! l1) 
      as R.
    destruct R.  
    symmetry in Hinscope.  
    apply fold_left__spec in Hinscope.
    destruct H11 as [J' | [J' | J']]; try solve [contradict J'; auto].
      destruct Hinscope as [Hinscope _].
      apply Hinscope.
      destruct J' as [J' _].
      destruct J' as [[cs2 [c1 [cs3 [J1 J2]]]] | [ps2 [p1 [ps3 [J1 J2]]]]]; 
        subst.
        rewrite getCmdsIDs_app. simpl. rewrite J2.
        apply in_or_app. right.
        apply in_or_app. left.
        apply in_or_app. right. simpl. auto.
    
        rewrite getPhiNodesIDs_app. simpl.
        apply in_or_app. left. 
        apply in_or_app. right. simpl. auto.
          
     unfold blockStrictDominates in J'.
     rewrite <- HeqR in J'.
     destruct block'.
     assert (In l0 (ListSet.set_diff eq_atom_dec bs_contents [l1])) as J.       
       destruct J' as [J1 J2].
       apply ListSet.set_diff_intro; auto.
         simpl. intro J. destruct J as [J | J]; auto.
     destruct Hinscope as [_ [Hinscope _]].
     assert (
       lookupBlockViaLabelFromFdef (fdef_intro (fheader_intro f t i0 a v) b) l0 =
       ret block_intro l0 p c t0) as J1.
       apply blockInFdefB_lookupBlockViaLabelFromFdef; auto.
         eapply lookupBlockViaIDFromFdef__blockInFdefB; eauto. 
     apply Hinscope with (b1:=block_intro l0 p c t0) in J; auto.
       apply J.
       eapply lookupBlockViaIDFromFdef__InGetBlockIDs; eauto.
Qed.

Lemma state_cmd_typing : forall TD ifs s m f b c defs id1 lc,
  NoDup (getBlockLocs b) ->
  isReachableFromEntry f b ->
  wf_insn ifs s m f b (insn_cmd c) ->
  Some defs = inscope_of_cmd f b c ->
  wf_defs TD f lc defs ->
  uniqFdef f ->
  In id1 (getInsnOperands (insn_cmd c)) ->
  exists t, exists gv, 
    lookupTypViaIDFromFdef f id1 = munit t /\
    lookupAL _ lc id1 = Some gv /\ wf_genericvalue TD gv t.
Proof.
  intros TD ifs s m f b c defs id1 lc Hnodup Hreach HwfInstr Hinscope HwfDefs 
    HuniqF HinOps.
  apply wf_insn__wf_insn_base in HwfInstr;
    try solve [unfold isPhiNode; simpl; auto].
  inv HwfInstr.  

  assert (
     In (f, b, insn_cmd c, id1)
     (unmake_list_fdef_block_insn_id
        (make_list_fdef_block_insn_id
           (map_list_id
              (fun id_ : id =>
               (f, b, insn_cmd c, id_))
              id_list)))
    ) as G.
    rewrite H5 in HinOps. clear - HinOps.
    induction id_list; simpl in *; auto.
      destruct HinOps as [HinOps | HinOps]; subst; auto.

  apply wf_operand_list__elim with (f1:=f)(b1:=b)(insn1:=insn_cmd c)(id1:=id1) 
    in H6; auto.

  inv H6. 
  eapply wf_defs_elim; eauto.
    unfold inscope_of_cmd in Hinscope.
    destruct b. destruct f. destruct f.
    remember ((dom_analyze (fdef_intro (fheader_intro f t0 i0 a v) b)) !! l0) 
      as R.
    destruct R.  
    symmetry in Hinscope.  
    apply fold_left__spec in Hinscope.
    destruct H11 as [J' | [J' | J']]; try solve [contradict J'; auto].
      destruct Hinscope as [Hinscope _].
      apply Hinscope.
      simpl in J'.
      destruct J' as [[ps2 [p1 [ps3 [J1 J2]]]] | [cs1 [c1 [cs2 [cs3 [J1 J2]]]]]];
        subst.

        rewrite getPhiNodesIDs_app. simpl.
        apply in_or_app. left. 
        apply in_or_app. right. simpl. auto.
          
        clear - J2 Hnodup.
        apply in_or_app. right.
        apply in_or_app. left. 
          simpl in Hnodup. apply NoDup_inv in Hnodup.
          destruct Hnodup as [_ Hnodup].
          apply NoDup_inv in Hnodup.
          destruct Hnodup as [Hnodup _].
          rewrite_env ((cs1 ++ c1 :: cs2) ++ c :: cs3).
          rewrite_env ((cs1 ++ c1 :: cs2) ++ c :: cs3) in Hnodup.
          apply NoDup__In_cmds_dominates_cmd; auto.
            rewrite getCmdsIDs_app.
            apply in_or_app. right. simpl. rewrite J2. simpl. auto.
    
     clear Hreach H0 HwfDefs.
     unfold blockStrictDominates in J'.
     rewrite <- HeqR in J'.
     destruct block'.
     assert (In l1 (ListSet.set_diff eq_atom_dec bs_contents [l0])) as J.       
       destruct J' as [J1 J2].
       apply ListSet.set_diff_intro; auto.
         simpl. intro J. destruct J as [J | J]; auto.
     destruct Hinscope as [_ [Hinscope _]].
     assert (
       lookupBlockViaLabelFromFdef (fdef_intro (fheader_intro f t0 i0 a v) b) l1
         = ret block_intro l1 p0 c1 t1) as J1.
       apply blockInFdefB_lookupBlockViaLabelFromFdef; auto.
         eapply lookupBlockViaIDFromFdef__blockInFdefB; eauto. 
     apply Hinscope with (b1:=block_intro l1 p0 c1 t1) in J; auto.
       apply J.
       eapply lookupBlockViaIDFromFdef__InGetBlockIDs; eauto.
Qed.

Lemma getOperandValue_inCmdOps_isnt_stuck : forall
  (s : system)
  (los : layouts)
  (nts : namedts)
  (ps : list product)
  (f : fdef)
  (cs : list cmd)
  (tmn : terminator)
  (lc : GVMap)
  (gl : GVMap)
  (Hwfg : wf_global (los,nts) s gl)
  (HwfSys1 : wf_system nil s)
  (HmInS1 : moduleInSystemB (module_intro los nts ps) s = true)
  (HfInPs : InProductsB (product_fdef f) ps = true)
  (l1 : l)
  (ps1 : phinodes)
  (cs1 : list cmd)
  (c : cmd)
  (Hreach : isReachableFromEntry f (block_intro l1 ps1 (cs1 ++ c :: cs) tmn))
  (HbInF : blockInFdefB (block_intro l1 ps1 (cs1 ++ c :: cs) tmn) f = true)
  (l0 : list atom)
  (HeqR : ret l0 = inscope_of_cmd f (block_intro l1 ps1 (cs1 ++ c :: cs) tmn) c)
  (Hinscope : wf_defs (los,nts) f lc l0)
  (v : value)
  (Hvincs : valueInCmdOperands v c),
  exists gv : GenericValue, getOperandValue (los, nts) v lc gl = ret gv.
Proof.
  intros.
  destruct v as [vid | vc]; simpl.
    assert (exists t, exists gv, 
                lookupTypViaIDFromFdef f vid = munit t /\
                lookupAL _ lc vid = Some gv /\ 
                wf_genericvalue (los,nts) gv t) as Hlkup.
      eapply state_cmd_typing; eauto. 
      eapply wf_system__uniq_block; eauto.
      eapply wf_system__wf_cmd; eauto using In_middle.
      eapply wf_system__uniqFdef; eauto.
      apply valueInCmdOperands__InOps; auto.
    destruct Hlkup as [gt [gv [Hlktyp [Hlkup Hwfgv]]]].
    simpl.
    rewrite Hlkup. eauto.

    assert (In c (cs1++c::cs)) as H. 
      apply in_or_app. simpl. auto.
    eapply wf_system__wf_cmd with (c:=c) in HbInF; eauto.
    eapply wf_cmd__wf_value with (v:=value_const vc) in HbInF; eauto.
    destruct HbInF as [t Hwfc].
    inv Hwfc.
    eapply const2GV_isnt_stuck with (S:=s)(t:=t); eauto.
Qed.

Lemma getOperandValue_inTmnOperans_isnt_stuck : forall
  (s : system)
  (los : layouts)
  (nts : namedts)
  (ps : list product)
  (f : fdef)
  (tmn : terminator)
  (lc : GVMap)
  (gl : GVMap)
  (Hwfg : wf_global (los,nts) s gl)
  (HwfSys1 : wf_system nil s)
  (HmInS1 : moduleInSystemB (module_intro los nts ps) s = true)
  (HfInPs : InProductsB (product_fdef f) ps = true)
  (l1 : l)
  (ps1 : phinodes)
  (cs1 : list cmd)
  (Hreach : isReachableFromEntry f (block_intro l1 ps1 cs1 tmn))
  (HbInF : blockInFdefB (block_intro l1 ps1 cs1 tmn) f = true)
  (l0 : list atom)
  (HeqR : ret l0 = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn) tmn)
  (Hinscope : wf_defs (los,nts) f lc l0)
  (v : value)
  (Hvincs : valueInTmnOperands v tmn),
  exists gv : GenericValue, getOperandValue (los, nts) v lc gl = ret gv.
Proof.
  intros.
  destruct v as [vid | vc].
    assert (HwfInstr:=HbInF).
    eapply wf_system__wf_tmn in HwfInstr; eauto.
    assert (exists t, exists gv, 
      lookupTypViaIDFromFdef f vid = munit t /\
      lookupAL _ lc vid = Some gv /\ 
      wf_genericvalue (los,nts) gv t) as Hlkup.
      eapply state_tmn_typing; eauto. 
      eapply wf_system__uniqFdef; eauto.
      apply valueInTmnOperands__InOps; auto.
    destruct Hlkup as [gt [gv [Hlktyp [Hlkup Hwfgv]]]].
    simpl.
    rewrite Hlkup. eauto.

    eapply wf_system__wf_tmn in HbInF; eauto.
    eapply wf_tmn__wf_value with (v:=value_const vc) in HbInF; eauto.
    destruct HbInF as [ct Hwfc].
    inv Hwfc.
    eapply const2GV_isnt_stuck with (S:=s)(t:=ct); eauto.
Qed.

Lemma values2GVs_isnt_stuck : forall
  l22
  (s : system)
  los nts
  (ps : list product)
  (f : fdef)
  (i0 : id)
  (i1 : inbounds)
  (t : typ)
  (v : value)
  (l2 : list_value)
  (cs : list cmd)
  (tmn : terminator)
  (lc : GVMap)
  (gl : GVMap)
  (Hwfg1 : wf_global (los,nts) s gl)
  (HwfSys1 : wf_system nil s)
  (HmInS1 : moduleInSystemB (module_intro los nts ps) s = true)
  (HfInPs : InProductsB (product_fdef f) ps = true)
  (l1 : l)
  (ps1 : phinodes)
  (cs1 : list cmd)
  (Hreach : isReachableFromEntry f
             (block_intro l1 ps1 (cs1 ++ insn_gep i0 i1 t v l2 :: cs) tmn))
  (HbInF : blockInFdefB
            (block_intro l1 ps1 (cs1 ++ insn_gep i0 i1 t v l2 :: cs) tmn) f =
          true)
  (l0 : list atom)
  (HeqR : ret l0 =
         inscope_of_cmd f
           (block_intro l1 ps1 (cs1 ++ insn_gep i0 i1 t v l2 :: cs) tmn)
           (insn_gep i0 i1 t v l2))
  (Hinscope : wf_defs (los,nts) f lc l0)
  (Hex : exists l21, l2 = app_list_value l21 l22),
  exists vidxs, values2GVs (los, nts) l22 lc gl = Some vidxs.
Proof.
  induction l22; intros; simpl; eauto.
    destruct Hex as [l21 Hex]; subst.
    assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl. unfold valueInListValue. right. 
        apply in_app_list_value_right; simpl; auto.

    destruct J as [gv J].
    rewrite J.         
    eapply IHl22 in HbInF; eauto.  
      destruct HbInF as [vidxs HbInF].
      rewrite HbInF. eauto.

      exists (app_list_value l21 (Cons_list_value v Nil_list_value)).
        rewrite cons_eq_app_list_value.
        rewrite cons_eq_app_list_value.
        apply app_list_value_assoc.
Qed.

Lemma wf_phinodes__getIncomingValuesForBlockFromPHINodes : forall
  (s : system)
  (los : layouts)
  (nts : namedts)
  (ps : list product)
  (f : fdef)
  l0
  (lc : GVMap)
  (gl : GVMap)
  (t : list atom)
  l1 ps1 cs1 tmn1
  (Hwfg : wf_global (los,nts) s gl)
  (HeqR : ret t = inscope_of_tmn f (block_intro l1 ps1 cs1 tmn1) tmn1)
  (Hinscope : wf_defs (los,nts) f lc t)
  (HuniqF : uniqFdef f)
  (ps' : phinodes)
  (cs' : cmds)
  (tmn' : terminator)
  ps2
  (Hreach : isReachableFromEntry f (block_intro l0 ps' cs' tmn'))
  (HbInF : blockInFdefB
            (block_intro l1 ps1 cs1 tmn1) f = true)
  (HwfB : wf_block nil s (module_intro los nts ps) f 
             (block_intro l1 ps1 cs1 tmn1))
  (H8 : wf_phinodes nil s (module_intro los nts ps) f
         (block_intro l0 ps' cs' tmn') ps2)
  (Hsucc : In l0 (successors_terminator tmn1))
  (Hin: exists ps1, ps' = ps1 ++ ps2),
   exists RVs : list (id * GenericValue),
     getIncomingValuesForBlockFromPHINodes (los, nts) ps2 
       (block_intro l1 ps1 cs1 tmn1) gl lc =
       ret RVs.
Proof.
  intros.
  induction ps2; simpl.
    exists nil. auto.
  
    destruct a. inv H8. inv H6.
    assert (exists v, getValueViaLabelFromValuels l2 l1 = Some v) as J.      
      clear - H14 HbInF HuniqF Hsucc.
      inv H14.
      unfold check_list_value_l in H0.
      remember (split (unmake_list_value_l l2)) as R.
      destruct R.
      destruct H0 as [J1 [J2 J3]].
      eapply In__getValueViaLabelFromValuels; eauto.
      destruct J2 as [_ J2].
      apply J2.
      eapply successors_predOfBlock; eauto.

    destruct J as [v J].
    rewrite J.
    destruct v as [vid | vc].
    Case "vid".
      assert (exists gv1, lookupAL GenericValue lc vid = Some gv1) as J1.
        Focus.
        destruct H14 as [Hwfops Hwfvls].             
        assert (Hnth:=J).
        eapply getValueViaLabelFromValuels__nth_list_value_l in Hnth; eauto.
        destruct Hnth as [n Hnth].
        assert (HwfV:=J).
        eapply wf_value_list__getValueViaLabelFromValuels__wf_value in HwfV; eauto.
        eapply wf_phi_operands__elim in Hwfops; eauto.
        destruct Hwfops as [Hneqid [vb [b1 [Hlkvb [Hlkb1 Hdom]]]]].
        assert (b1 = block_intro l1 ps1 cs1 tmn1) 
          as EQ.
          clear - Hlkb1 HbInF HuniqF.
          apply blockInFdefB_lookupBlockViaLabelFromFdef in HbInF; auto.
          rewrite HbInF in Hlkb1. inv Hlkb1; auto.

        subst.
        clear - Hdom Hinscope HeqR J Hreach H2 HbInF Hlkvb Hlkb1 HuniqF.
        destruct Hdom as [J3 | J3]; try solve [contradict Hreach; auto].
        clear Hreach.        
        unfold blockDominates in J3.         
        destruct vb.
        unfold inscope_of_tmn in HeqR.
        destruct f. destruct f.
        remember ((dom_analyze (fdef_intro (fheader_intro f t2 i0 a v) b)) !! l1)
          as R1.
        destruct R1.
        symmetry in HeqR.    
        apply fold_left__spec in HeqR.
        destruct (eq_atom_dec l3 l1); subst.
        SCase "l3=l1".
          destruct HeqR as [HeqR _].
          assert (In vid t) as G.
            clear - J HeqR Hlkb1 J3 Hlkvb HbInF HuniqF.
            assert (J':=Hlkvb).
            apply lookupBlockViaIDFromFdef__blockInFdefB in Hlkvb.
            apply lookupBlockViaLabelFromFdef_inv in Hlkb1; auto.
            destruct Hlkb1 as [J1 J2].
            eapply blockInFdefB_uniq in J2; eauto.
            destruct J2 as [J2 [J4 J5]]; subst.
            apply lookupBlockViaIDFromFdef__InGetBlockIDs in J'.
            simpl in J'.
            apply HeqR.
            rewrite_env ((getPhiNodesIDs ps1 ++ getCmdsIDs cs1)++getArgsIDs a).
            apply in_or_app; auto.       
          apply wf_defs_elim with (id1:=vid) in Hinscope; auto.
          destruct Hinscope as [? [gv1 [? [Hinscope ?]]]].
          exists gv1. auto.

        SCase "l3<>l1".
          assert (In l3 (ListSet.set_diff eq_atom_dec bs_contents [l1])) as G.
            apply ListSet.set_diff_intro; auto.
              simpl. intro JJ. destruct JJ as [JJ | JJ]; auto.
          assert (
            lookupBlockViaLabelFromFdef 
              (fdef_intro (fheader_intro f t2 i0 a v) b) l3 = 
              ret block_intro l3 p c t1) as J1.
            clear - Hlkvb HuniqF.
            apply lookupBlockViaIDFromFdef__blockInFdefB in Hlkvb.
            apply blockInFdefB_lookupBlockViaLabelFromFdef in Hlkvb; auto.
          destruct HeqR as [_ [HeqR _]].
          apply HeqR in J1; auto.
          assert (In vid t) as InVid.
            clear - J1 HeqR Hlkb1 J3 Hlkvb HbInF HuniqF.
            apply J1.
            apply lookupBlockViaIDFromFdef__InGetBlockIDs in Hlkvb; auto.
          apply wf_defs_elim with (id1:=vid) in Hinscope; auto.
          destruct Hinscope as [? [gv1 [? [Hinscope ?]]]].
          exists gv1. auto.
        Unfocus.
  
      destruct J1 as [gv1 J1].
      simpl. rewrite J1. 
      apply IHps2 in H7.
        destruct H7 as [RVs H7].
        rewrite H7. 
        exists ((i0, gv1) :: RVs). auto.
  
        destruct Hin as [ps3 Hin]. subst.
        exists (ps3++[insn_phi i0 t0 l2]).
        simpl_env. auto.
  
    Case "vc".
      eapply wf_value_list__getValueViaLabelFromValuels__wf_value in H2; eauto.
      inv H2.
      destruct (@const2GV_isnt_stuck (los,nts) s gl vc t0); auto.
      simpl. rewrite H.
      apply IHps2 in H7.
        destruct H7 as [RVs H7].
        rewrite H7. 
        exists ((i0, x) :: RVs). auto.
  
        destruct Hin as [ps3 Hin]. subst.
        exists (ps3++[insn_phi i0 t0 l2]).
        simpl_env. auto.
Qed.

Lemma params2GVs_isnt_stuck : forall
  p22
  (s : system)
  los nts
  (ps : list product)
  (f : fdef)
  (i0 : id)
  n c t v p2
  (cs : list cmd)
  (tmn : terminator)
  (lc : GVMap)
  (gl : GVMap)
  (Hwfg1 : wf_global (los,nts) s gl)
  (HwfSys1 : wf_system nil s)
  (HmInS1 : moduleInSystemB (module_intro los nts ps) s = true)
  (HfInPs : InProductsB (product_fdef f) ps = true)
  (l1 : l)
  (ps1 : phinodes)
  (cs1 : list cmd)
  (Hreach : isReachableFromEntry f
             (block_intro l1 ps1 (cs1 ++ insn_call i0 n c t v p2 :: cs) tmn))
  (HbInF : blockInFdefB
            (block_intro l1 ps1 (cs1 ++ insn_call i0 n c t v p2 :: cs) tmn) f =
          true)
  (l0 : list atom)
  (HeqR : ret l0 =
         inscope_of_cmd f
           (block_intro l1 ps1 (cs1 ++ insn_call i0 n c t v p2 :: cs) tmn)
           (insn_call i0 n c t v p2))
  (Hinscope : wf_defs (los,nts) f lc l0)
  (Hex : exists p21, p2 = p21 ++ p22),
  exists gvs, params2GVs (los, nts) p22 lc gl = Some gvs.
Proof.
  induction p22; intros; simpl; eauto.

    destruct a.
    destruct Hex as [p21 Hex]; subst.
    assert (exists gv, getOperandValue (los, nts) v0 lc gl = Some gv) as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl. unfold valueInParams. right. 
        assert (J:=@in_split_r _ _ (p21 ++ (t0, v0) :: p22) (t0, v0)).
        remember (split (p21 ++ (t0, v0) :: p22)) as R.
        destruct R.
        simpl in J. apply J.
        apply In_middle.
    destruct J as [gv J]. 
    rewrite J.         
    eapply IHp22 in HbInF; eauto.  
      destruct HbInF as [vidxs HbInF].
      rewrite HbInF. eauto.

      exists (p21 ++ [(t0,v0)]). simpl_env. auto.
Qed.

Definition undefined_state S : Prop :=
  match S with
  | {| CurTargetData := td;
       ECS := {|
                CurCmds := nil;
                Terminator := insn_return _ _ _;
                Allocas := als |} :: 
              {| CurCmds := c::_ |} :: _;
       Mem := M |} => free_allocas td M als = None
  | _ => False
  end \/
  match S with
  | {| CurTargetData := td;
       ECS := {|
                CurBB := _;
                CurCmds := nil;
                Terminator := insn_return_void _;
                Allocas := als |} :: 
              {| CurCmds := c::_ |} :: _;
       Mem := M |} => free_allocas td M als = None \/ 
                      match getCallerReturnID c with
                      | Some _ => True
                      | _ => False
                      end
  | _ => False
  end \/
  match S with
  | {| ECS := {|
                CurBB := block_intro _ _ _ (insn_unreachable _);
                CurCmds := nil;
                Terminator := (insn_unreachable _)
               |} :: _
     |} => True
  | _ => False
  end \/
  match S with
  | {| CurTargetData := td;
       ECS := {| CurCmds := insn_malloc _ t v a::_ ; Locals := lc|} :: _;
       Globals := gl;
       Mem := M |}
  | {| CurTargetData := td;
       ECS := {| CurCmds := insn_alloca _ t v a::_ ; Locals := lc|} :: _;
       Globals := gl;
       Mem := M |} =>
       match getOperandValue td v lc gl with
       | Some gv =>
           match getTypeAllocSize td t with
           | Some asz =>
               match malloc td M asz gv a with
               | None => True
               | _ => False
               end
           | _ => False
           end
       | _ => False
       end
  | _ => False
  end \/
  match S with
  | {| CurTargetData := td;
       ECS := {| CurCmds := insn_free _ _ v::_ ; Locals := lc|} :: _;
       Globals := gl;
       Mem := M |} =>
       match getOperandValue td v lc gl with
       | Some gv =>
           match free td M gv with
           | None => True
           | _ => False
           end
       | _ => False
       end
  | _ => False
  end \/
  match S with
  | {| CurTargetData := td;
       ECS := {| CurCmds := insn_load _ t v a::_ ; Locals := lc|} :: _;
       Globals := gl;
       Mem := M |} =>
       match getOperandValue td v lc gl with
       | Some gv =>
           match mload td M gv t a with
           | None => True
           | _ => False
           end
       | _ => False
       end
  | _ => False
  end \/
  match S with
  | {| CurTargetData := td;
       ECS := {| CurCmds := insn_store _ t v v0 a::_ ; Locals := lc|} :: _;
       Globals := gl;
       Mem := M |} =>
       match getOperandValue td v lc gl, getOperandValue td v0 lc gl with
       | Some gv, Some mgv =>
           match mstore td M mgv t gv a with
           | None => True
           | _ => False
           end
       | _, _ => False
       end
  | _ => False
  end \/
  match S with
  | {| CurTargetData := td;
       CurProducts := ps;
       ECS := {| CurCmds := insn_call i0 n _ ft v p::_ ; Locals := lc|} :: _;
       Globals := gl;
       FunTable := fs;
       Mem := M |} =>
       match lookupFdefViaGV td ps gl lc fs v, 
             lookupExFdecViaGV td ps gl lc fs v with
       | None, Some (fdec_intro (fheader_intro fa rt fid la va)) =>
           match params2GVs td p lc gl with
           | Some gvs =>
             match callExternalFunction M fid gvs with
             | Some (oresult, _) =>
                match exCallUpdateLocals td ft n i0 oresult lc with
                | None => True
                | _ => False
                end
             | None => True
             end
           | _ => False
           end
       | None, None => True
       | _, _ => False
       end
  | _ => False
  end.

Ltac undefbehave := unfold undefined_state; simpl; 
  try solve [
    auto | 
    right; auto | 
    right; right; auto |  
    right; right; right; right; auto |
    right; right; right; right; right; auto |
    right; right; right; right; right; right; auto |
    right; right; right; right; right; right; right; auto |
    right; right; right; right; right; right; right; right; auto
  ].

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

Lemma initializeFrameValues__total_aux : forall los nts Ps s ifs fattr ft fid va 
  bs2 la2 la1 lc1 
  (HwfF: wf_fdef ifs s (module_intro los nts Ps) 
    (fdef_intro (fheader_intro fattr ft fid (la1 ++ la2) va) bs2))
  gvs2,
  exists lc2, _initializeFrameValues (los,nts) la2 gvs2 lc1 = Some lc2.
Proof.
  induction la2; simpl in *; intros.
    eauto.

    destruct a. destruct p.
    assert (HwfF':=HwfF).
    simpl_env in HwfF'.
    rewrite_env ((la1 ++ [(t, a, i0)]) ++ la2) in HwfF'.
    inv HwfF.
    assert (In (t, a, i0)
            (map_list_typ_attributes_id
              (fun (typ_ : typ) (attributes_ : attributes) (id_ : id) =>
              (typ_, attributes_, id_)) typ_attributes_id_list)) as JJ.
    rewrite <- H11.
    apply in_or_app; simpl; auto.
    apply wf_typ_list__in_args__wf_typ with (t:=t)(a:=a)(i0:=i0) in H12; 
      auto.
    apply feasible_typ_list__in_args__feasible_typ with (t:=t)(a:=a)(i0:=i0) 
      in H13; auto.   
    destruct gvs2.
      apply IHla2 with (gvs2:=nil)(lc1:=lc1) in HwfF'.
      destruct HwfF' as [lc2 J].
      rewrite J. 
      apply gundef__total' in H13. 
      destruct H13 as [gv H13]. rewrite H13.
      eauto.

      apply IHla2 with (gvs2:=gvs2)(lc1:=lc1) in HwfF'.
      destruct HwfF' as [lc2 J].
      rewrite J. inv H13.
      apply fit_gv__total with (gv1:=g) in H; auto.
      destruct H as [gv H]. rewrite H.
      eauto.
Qed.

Lemma initLocal__total : forall los nts Ps s ifs fattr ft fid va bs2 la2  
  (HwfF: wf_fdef ifs s (module_intro los nts Ps) 
    (fdef_intro (fheader_intro fattr ft fid la2 va) bs2))
  gvs2,
  exists lc2, initLocals (los,nts) la2 gvs2 = Some lc2.
Proof.
  intros.
  unfold initLocals.
  eapply initializeFrameValues__total_aux with (la1:=nil); eauto.
Qed.

Lemma wf_trunc__wf_typ : forall ifs s los nts ps f b i0 t t0 v t1,
  wf_trunc ifs s (module_intro los nts ps) f b 
    (insn_cmd (insn_trunc i0 t t0 v t1)) ->
  wf_typ s t1 /\ feasible_typ (los, nts) t1.
Proof.
  intros.
  inv H; auto.
Qed.

Lemma progress : forall S1,
  wf_State S1 -> 
  ds_isFinialState S1 = true \/ 
  (exists S2, exists tr, dsInsn S1 S2 tr) \/
  undefined_state S1.
Proof.
  intros S1 HwfS1.
  destruct S1 as [s [los nts] ps ecs gl fs M].
  destruct HwfS1 as [Hwfg1 [HwfSys1 [HmInS1 HwfECs]]].
  destruct ecs; try solve [inversion HwfECs].
  destruct e as [f b cs tmn lc als].
  destruct HwfECs as [[Hreach 
                       [HbInF [HfInPs [Hwflc [Hinscope [l1 [ps1 [cs1 Heq]]]]]]]] 
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
        assert (J:=HbInF).
        apply HwfCall in J. clear HwfCall.
        destruct cs'; try solve [inversion J].
        destruct c; try solve [inversion J]. clear J.
        remember (free_allocas (los,nts) M als) as Rm.
        destruct Rm as [M' |]; try solve [undefbehave].
        left. symmetry in HeqRm.
        rename HeqRm into J.
        assert (exists lc'', 
          returnUpdateLocals (los,nts) (insn_call i1 n c t0 v0 p) v lc lc' gl
            = Some lc'') as Hretup.
          unfold returnUpdateLocals. simpl.
          assert (exists gv : GenericValue, 
            getOperandValue (los, nts) v lc gl = ret gv) as H.
            eapply getOperandValue_inTmnOperans_isnt_stuck; eauto.
              simpl. auto.
          destruct H as [gv H]. rewrite H.
          destruct n.
            exists lc'. auto.

            destruct HwfECs as [[Hreach' 
              [HbInF' [HfInPs' [Hwflc' [Hinscope' [l1' [ps1' [cs1' Heq']]]]]]]] 
              [HwfECs HwfCall]]; subst.
            eapply wf_system__wf_cmd with (c:=insn_call i1 false c t0 v0 p) 
              in HbInF'; eauto using in_middle.
            inv HbInF'.
            inv H6.
            assert (exists gv0, fit_gv (layouts5, namedts5) typ1 gv = Some gv0)
              as G.
              inv H17.
              apply fit_gv__total; auto.
            destruct G as [gv0 G].
            rewrite G. eauto.
          
        destruct Hretup as [lc'' Hretup].
        exists (mkState s (los, nts) ps ((mkEC f' b' cs' tmn' lc'' als')::
           ecs) gl fs M').
        exists trace_nil.
        eauto.  

    SCase "tmn=ret void".
      simpl in HwfCall.
      destruct ecs.
        simpl; auto.      

        right.
        destruct e as [f' b' cs' tmn' lc' als'].
        assert (J:=HbInF).
        apply HwfCall in J. clear HwfCall.
        destruct cs'; try solve [inversion J].
        destruct c; try solve [inversion J]. clear J.
        remember (free_allocas (los,nts) M als) as Rm.
        destruct Rm as [M' |]; try solve [undefbehave].
        symmetry in HeqRm.
        rename HeqRm into J.
        destruct n; try solve [undefbehave].
        left.
        exists (mkState s (los, nts) ps ((mkEC f' b' cs' tmn' lc' als')::
              ecs) gl fs M').
        exists trace_nil.
        eauto.  

    SCase "tmn=br". 
      right. left.
      assert (uniqFdef f) as HuniqF.
        eapply wf_system__uniqFdef; eauto.
      assert (exists c, getOperandValue (los,nts) v lc gl = Some c) as Hget.
        eapply getOperandValue_inTmnOperans_isnt_stuck; eauto.
          simpl. auto.
      destruct Hget as [c Hget].
      assert (exists l', exists ps', exists cs', exists tmn',
              Some (block_intro l' ps' cs' tmn') = 
              (if isGVZero (los,nts) c
                 then lookupBlockViaLabelFromFdef f l3
                 else lookupBlockViaLabelFromFdef f l2)) as HlkB.
        eapply wf_system__wf_tmn in HbInF; eauto.
        inv HbInF. 
        destruct block1 as [l2' ps2 cs2 tmn2].
        destruct block2 as [l3' ps3 cs3 tmn3].
        destruct (isGVZero (los, nts) c).
          exists l3'. exists ps3. exists cs3. exists tmn3.
          rewrite H11. auto.

          exists l2'. exists ps2. exists cs2. exists tmn2.
          rewrite H10. auto.

      destruct HlkB as [l' [ps' [cs' [tmn' HlkB]]]].
      assert (exists lc', switchToNewBasicBlock (los, nts) 
        (block_intro l' ps' cs' tmn') 
        (block_intro l1 ps1 (cs1++nil) (insn_br i0 v l2 l3)) gl lc = 
          Some lc') as Hswitch.
         assert (exists RVs, 
           getIncomingValuesForBlockFromPHINodes (los, nts) ps'
             (block_intro l1 ps1 (cs1++nil) (insn_br i0 v l2 l3)) gl lc =
           Some RVs) as J.
           assert (HwfB := HbInF).
           eapply wf_system__blockInFdefB__wf_block in HwfB; eauto.
           simpl_env in *.
           destruct (isGVZero (los, nts) c).
             assert (J:=HlkB).
             symmetry in J.
             apply lookupBlockViaLabelFromFdef_inv in J; auto.
             destruct J as [Heq J]; subst.
             eapply wf_system__lookup__wf_block in HlkB; eauto.
             inv HlkB. clear H9 H10.
             eapply wf_phinodes__getIncomingValuesForBlockFromPHINodes 
               with (ps':=ps')(cs':=cs')(tmn':=tmn')(l0:=l'); eauto.
               apply reachable_successors with (l0:=l1)(cs:=ps1)(ps:=cs1)
                 (tmn:=insn_br i0 v l2 l'); simpl; auto.
               simpl. auto.    
               exists nil. auto.

             assert (J:=HlkB).
             symmetry in J.
             apply lookupBlockViaLabelFromFdef_inv in J; auto.
             destruct J as [Heq J]; subst.
             eapply wf_system__lookup__wf_block in HlkB; eauto.
             inv HlkB. clear H9 H10.
             eapply wf_phinodes__getIncomingValuesForBlockFromPHINodes 
               with (ps':=ps')(cs':=cs')(tmn':=tmn')(l0:=l'); eauto.
               apply reachable_successors with (l0:=l1)(cs:=ps1)(ps:=cs1)
                 (tmn:=insn_br i0 v l' l3); simpl; auto.
               simpl. auto.    
               exists nil. auto.
         
         destruct J as [RVs J].
         unfold switchToNewBasicBlock. simpl.
         rewrite J. 
         exists (updateValuesForNewBlock RVs lc). auto.

      destruct Hswitch as [lc' Hswitch].
      exists (mkState s (los, nts) ps 
              ((mkEC f (block_intro l' ps' cs' tmn') cs' tmn' lc' als)
              ::ecs) gl fs M).
      exists trace_nil. eauto.

    SCase "tmn=br_uncond". 
      right. left.
      assert (uniqFdef f) as HuniqF.
        eapply wf_system__uniqFdef; eauto.
      assert (exists ps', exists cs', exists tmn',
        Some (block_intro l2 ps' cs' tmn') = lookupBlockViaLabelFromFdef f l2) 
          as HlkB.
        eapply wf_system__wf_tmn in HbInF; eauto.
        inv HbInF.        
        exists ps1. exists (cs1++nil). exists (insn_br_uncond i0 l2).
        rewrite H6. 
        apply lookupBlockViaLabelFromFdef_inv in H6; auto.
        destruct H6 as [H6 _]; subst. auto.

      destruct HlkB as [ps' [cs' [tmn' HlkB]]].

      assert (exists lc', switchToNewBasicBlock (los, nts) 
        (block_intro l2 ps' cs' tmn') 
        (block_intro l1 ps1 (cs1 ++ nil) (insn_br_uncond i0 l2)) gl lc = 
          Some lc') as Hswitch.
         assert (exists RVs, 
           getIncomingValuesForBlockFromPHINodes (los, nts) ps'
             (block_intro l1 ps1 (cs1 ++ nil) (insn_br_uncond i0 l2)) gl lc =
           Some RVs) as J.
           assert (HwfB := HbInF).
           eapply wf_system__blockInFdefB__wf_block in HwfB; eauto.
           eapply wf_system__lookup__wf_block in HlkB; eauto.
           inv HlkB. clear H9 H10.
           eapply wf_phinodes__getIncomingValuesForBlockFromPHINodes 
             with (l0:=l2); eauto.      
             apply reachable_successors with (l0:=l1)(cs:=ps1)(ps:=cs1++nil)
               (tmn:=insn_br_uncond i0 l2); simpl; auto.
             simpl. auto.
             exists nil. auto.
         
         destruct J as [RVs J].
         unfold switchToNewBasicBlock. simpl.
         rewrite J. 
         exists (updateValuesForNewBlock RVs lc). auto.

      destruct Hswitch as [lc' Hswitch].
      exists (mkState s (los, nts) ps 
              ((mkEC f (block_intro l2 ps' cs' tmn') cs' tmn' lc' als)
              ::ecs) gl fs M).
      exists trace_nil. eauto.

    SCase "tmn=unreachable".
      undefbehave.

  Case "cs<>nil".
    assert (wf_insn nil s (module_intro los nts ps) f 
      (block_intro l1 ps1 (cs1 ++ c :: cs) tmn) (insn_cmd c)) as Hwfc.
      assert (In c (cs1++c::cs)) as H. 
        apply in_or_app. simpl. auto.
      eapply wf_system__wf_cmd with (c:=c) in HbInF; eauto.
    remember (inscope_of_cmd f (block_intro l1 ps1 (cs1 ++ c :: cs) tmn) c) as R.
    destruct R; try solve [inversion Hinscope].
    right.
    destruct c.
  SCase "c=bop".
    left.
    assert (exists gv3, BOP (los,nts) lc gl b s0 v v0 = Some gv3) as Hinsn_bop.
      unfold BOP.      
      assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      assert (exists gv, getOperandValue (los, nts) v0 lc gl = Some gv) as J0.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
          destruct J as [gv J].
      destruct J0 as [gv0 J0].
      rewrite J. rewrite J0. 
      unfold mbop. inv Hwfc.
      apply wf_value__wf_typ in H7. destruct H7 as [J1 J2]. inv J2.
      destruct (GV2val (los, nts) gv); eauto using gundef__total.
      destruct v1; eauto using gundef__total.
      destruct (GV2val (los, nts) gv0); eauto using gundef__total.
      destruct v1; eauto using gundef__total.
      destruct (eq_nat_dec (wz + 1) (Size.to_nat s0)); 
        eauto using gundef__total.
      destruct b; eauto using gundef__total.
    destruct Hinsn_bop as [gv3 Hinsn_bop].
    exists 
         {|
         CurSystem := s;
         CurTargetData := (los, nts);
         CurProducts := ps;
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_bop i0 b s0 v v0 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv3);
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M |}.
     exists trace_nil. eauto.

  SCase "c=fbop". 
    left.
    assert (exists gv3, FBOP (los,nts) lc gl f0 f1 v v0 = Some gv3) 
      as Hinsn_fbop.
      unfold FBOP.      
      assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      assert (exists gv, getOperandValue (los, nts) v0 lc gl = Some gv) as J0.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      destruct J0 as [gv0 J0].
      rewrite J. rewrite J0. 
      unfold mfbop. inv Hwfc.
      apply wf_value__wf_typ in H7. destruct H7 as [J1 J2]. inv J2.
      destruct (GV2val (los, nts) gv); eauto using gundef__total.
      destruct v1; eauto using gundef__total.
      destruct (GV2val (los, nts) gv0); eauto using gundef__total.
      destruct v1; eauto using gundef__total.
      destruct f1; try solve [eauto | inversion J1].

    destruct Hinsn_fbop as [gv3 Hinsn_fbop].
    exists 
         {|
         CurSystem := s;
         CurTargetData := (los, nts);
         CurProducts := ps;
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_fbop i0 f0 f1 v v0 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv3);
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M |}.
     exists trace_nil. eauto.

  SCase "c=extractvalue".
    left.
    assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gv J].
    assert (exists gv', extractGenericValue (los, nts) t gv l2 = Some gv') as J'.
      unfold extractGenericValue.
      inv Hwfc. destruct H13 as [idxs [o [J1 J2]]].
      rewrite J1. rewrite J2. inv H15.
      destruct (mget (los, nts) gv o typ'); eauto using gundef__total.
    destruct J' as [gv' J'].
    exists 
         {|
         CurSystem := s;
         CurTargetData := (los, nts);
         CurProducts := ps;
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_extractvalue i0 t v l2 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv');
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M |}.
     exists trace_nil. eauto.

  SCase "c=insertvalue".
    left.
    assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gv J].
    assert (exists gv', getOperandValue (los, nts) v0 lc gl = Some gv') as J'.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J' as [gv' J'].
    assert (exists gv'', insertGenericValue (los, nts) t gv l2 t0 gv' = 
      Some gv'') as J''.
      unfold insertGenericValue.
      inv Hwfc. destruct H16 as [idxs [o [J1 J2]]].
      rewrite J1. rewrite J2.
      apply wf_value__wf_typ in H10. destruct H10 as [J3 J4]. inv J4.
      destruct (mset (los, nts) gv o t0 gv'); eauto using gundef__total.
    destruct J'' as [gv'' J''].
    exists 
         {|
         CurSystem := s;
         CurTargetData := (los, nts);
         CurProducts := ps;
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_insertvalue i0 t v t0 v0 l2 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv'');
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M |}.
     exists trace_nil. eauto.

  SCase "c=malloc". 
    inv Hwfc. inv H12.
    apply feasible_typ_inv'' in H.
    destruct H as [ssz [asz [J1 J2]]].
    assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gv J].
    remember (malloc (los, nts) M asz gv a) as R.
    destruct R as [[M' mb] |].
      left.
      exists 
         {|
         CurSystem := s;
         CurTargetData := (los, nts);
         CurProducts := ps;
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_malloc i0 t v a :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 (blk2GV (los, nts) mb));
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M' |}.
      exists trace_nil.
      eauto.      
      
      unfold undefined_state.
      right. rewrite J. rewrite J2. rewrite <- HeqR0. undefbehave.

  SCase "free". 
    assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gv J].
    remember (free (los, nts) M gv) as R.
    destruct R as [M'|].
      left.
      exists 
         {|
         CurSystem := s;
         CurTargetData := (los, nts);
         CurProducts := ps;
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_free i0 t v :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := lc;
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M' |}.
      exists trace_nil.
      eauto.      
      
      unfold undefined_state.
      right. rewrite J. rewrite <- HeqR0. undefbehave.

  SCase "alloca".
    inv Hwfc. inv H12.
    apply feasible_typ_inv'' in H.
    destruct H as [ssz [asz [J1 J2]]].
    assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gv J].
    remember (malloc (los, nts) M asz gv a) as R.
    destruct R as [[M' mb] |].
      left.
      exists 
         {|
         CurSystem := s;
         CurTargetData := (los, nts);
         CurProducts := ps;
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_alloca i0 t v a :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 (blk2GV (los, nts) mb));
                Allocas := (mb::als) |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M' |}.
      exists trace_nil.
      eauto.      
      
      right.
      unfold undefined_state.
      right. rewrite J. rewrite J2. rewrite <- HeqR0. undefbehave.

  SCase "load".
    assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gv J].
    remember (mload (los, nts) M gv t a) as R.
    destruct R as [gv'|].
      left.
      exists 
         {|
         CurSystem := s;
         CurTargetData := (los, nts);
         CurProducts := ps;
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_load i0 t v a :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := updateAddAL _ lc i0 gv';
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M |}.
      exists trace_nil.
      eauto.      

      right.
      unfold undefined_state.
      right. rewrite J. rewrite <- HeqR0. undefbehave.
      
  SCase "store".
    assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gv J].
    assert (exists gv, getOperandValue (los, nts) v0 lc gl = Some gv) as J0.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J0 as [mgv J0].
    remember (mstore (los, nts) M mgv t gv a) as R.
    destruct R as [M'|].
      left.
      exists 
         {|
         CurSystem := s;
         CurTargetData := (los, nts);
         CurProducts := ps;
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_store i0 t v v0 a :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := lc;
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M' |}.
      exists trace_nil.
      eauto.      

      right.
      unfold undefined_state.
      right. rewrite J. rewrite J0. rewrite <- HeqR0. undefbehave.

  SCase "gep".
    assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [mp J].
    assert (exists vidxs, values2GVs (los, nts) l2 lc gl = Some vidxs) as J2.
      eapply values2GVs_isnt_stuck; eauto.
        exists Nil_list_value. auto.
    destruct J2 as [vidxs J2].
    inv Hwfc.
    assert (exists mp', GEP (los, nts) t mp vidxs i1 typ' = Some mp') as J3.
      unfold GEP. inv H17.
      destruct (GV2ptr (los, nts) (getPointerSize (los, nts)) mp); 
        eauto using gundef__total.
      destruct (GVs2Nats (los, nts) vidxs); eauto using gundef__total.
      destruct (mgep (los, nts) t v0 l3); eauto using gundef__total.
    destruct J3 as [mp' J3].
    left.
    exists 
         {|
         CurSystem := s;
         CurTargetData := (los, nts);
         CurProducts := ps;
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_gep i0 i1 t v l2 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 mp');
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M |}.
     exists trace_nil. eauto.

  SCase "trunc".
    left.
    assert (exists gv2, TRUNC (los,nts) lc gl t t0 v t1 = Some gv2) 
      as Hinsn_trunc.
      unfold TRUNC.      
      assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      rewrite J.
      unfold mtrunc. inv Hwfc.
      assert (H5':=H5).
      apply wf_trunc__wf_typ in H5'. destruct H5' as [J1 J2]. inv J2.
      destruct (GV2val (los, nts) gv); eauto using gundef__total.
      inv H5; try solve [destruct v0; eauto using gundef__total].
        rewrite H16.
        destruct v0; eauto using gundef__total.
          destruct floating_point2; try solve [eauto | inversion H14].
    destruct Hinsn_trunc as [gv2 Hinsn_trunc].
    exists 
         {|
         CurSystem := s;
         CurTargetData := (los, nts);
         CurProducts := ps;
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_trunc i0 t t0 v t1 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv2);
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M |}.
     exists trace_nil. eauto.

  SCase "ext".
    left.
    assert (exists gv2, EXT (los,nts) lc gl e t v t0 = Some gv2) 
      as Hinsn_ext.
      unfold EXT.      
      assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      rewrite J.
      unfold mext. 
      inv Hwfc. 
      inv H5; try solve 
        [destruct (GV2val (los, nts) gv); eauto using gundef__total'; 
         destruct v0; eauto using gundef__total'].
        rewrite H15.
        destruct (GV2val (los, nts) gv); eauto using gundef__total'; 
        destruct v0; eauto using gundef__total'.
        destruct floating_point2; try solve [inversion H13 | eauto].
    destruct Hinsn_ext as [gv2 Hinsn_ext].
    exists 
         {|
         CurSystem := s;
         CurTargetData := (los, nts);
         CurProducts := ps;
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_ext i0 e t v t0 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv2);
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M |}.
     exists trace_nil. eauto.

  SCase "cast". 
    left.
    assert (exists gv2, CAST (los,nts) lc gl c t v t0 = Some gv2) 
      as Hinsn_cast.
      unfold CAST.      
      assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      rewrite J.
      unfold mcast, mptrtoint, mbitcast.
      inv Hwfc. 
      inv H5; eauto using gundef__total'.
      
    destruct Hinsn_cast as [gv2 Hinsn_cast].
    exists 
         {|
         CurSystem := s;
         CurTargetData := (los, nts);
         CurProducts := ps;
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_cast i0 c t v t0 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv2);
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M |}.
     exists trace_nil. eauto.

  SCase "icmp".
    left.
    assert (exists gv2, ICMP (los,nts) lc gl c t v v0 = Some gv2) 
      as Hinsn_icmp.
      unfold ICMP.      
      assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      rewrite J.
      assert (exists gv, getOperandValue (los, nts) v0 lc gl = Some gv) as J0.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J0 as [gv0 J0].
      rewrite J0.
      unfold micmp.
      inv Hwfc. 
      unfold isPointerTyp in H14. unfold is_true in H14.
      unfold micmp_int.
      destruct H14 as [H14 | H14].
        destruct t; try solve [simpl in H14; contradict H14; auto].
        destruct (GV2val (los,nts) gv); eauto using gundef__total.
        destruct v1; eauto using gundef__total.
        destruct (GV2val (los,nts) gv0); eauto using gundef__total.
        destruct v1; eauto using gundef__total.
        destruct c; eauto using gundef__total.

        destruct t; try solve [simpl in H14; contradict H14; auto]. 
          eauto using gundef__total.
(*      destruct (mptrtoint (los, nts) M gv Size.ThirtyTwo); eauto.
        destruct (mptrtoint (los, nts) M gv0 Size.ThirtyTwo); eauto.
        destruct (GV2val (los, nts) g); eauto.
        destruct v1; eauto.
        destruct (GV2val (los, nts) g0); eauto.
        destruct v1; eauto.
        destruct c; eauto. *)
    destruct Hinsn_icmp as [gv2 Hinsn_icmp].
    exists 
         {|
         CurSystem := s;
         CurTargetData := (los, nts);
         CurProducts := ps;
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_icmp i0 c t v v0 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv2);
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M |}.
     exists trace_nil. eauto.

  SCase "fcmp".
    left.
    assert (exists gv2, FCMP (los,nts) lc gl f0 f1 v v0 = Some gv2) 
      as Hinsn_fcmp.
      unfold FCMP.      
      assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) as J.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J as [gv J].
      rewrite J.
      assert (exists gv, getOperandValue (los, nts) v0 lc gl = Some gv) as J0.
        eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
          simpl; auto.
      destruct J0 as [gv0 J0].
      rewrite J0.
      unfold mfcmp.
      inv Hwfc. 
      destruct (GV2val (los, nts) gv); eauto using gundef__total.
      destruct v1; eauto using gundef__total.
      destruct (GV2val (los, nts) gv0); eauto using gundef__total.
      destruct v1; eauto using gundef__total.
      apply wf_value__wf_typ in H12.
      destruct H12 as [J1 J2].
      destruct f1; try solve [eauto | inversion J1].
        destruct f0; try solve [eauto | inversion H9].
        destruct f0; try solve [eauto | inversion H9].
    destruct Hinsn_fcmp as [gv2 Hinsn_fcmp].
    exists 
         {|
         CurSystem := s;
         CurTargetData := (los, nts);
         CurProducts := ps;
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_fcmp i0 f0 f1 v v0 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (updateAddAL _ lc i0 gv2);
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M |}.
     exists trace_nil. eauto.

  SCase "select".
    assert (exists gv, getOperandValue (los, nts) v lc gl = Some gv) as J.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J as [gv J].
    assert (exists gv0, getOperandValue (los, nts) v0 lc gl = Some gv0) as J0.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J0 as [gv0 J0].
    assert (exists gv1, getOperandValue (los, nts) v1 lc gl = Some gv1) as J1.
      eapply getOperandValue_inCmdOps_isnt_stuck; eauto.
        simpl; auto.
    destruct J1 as [gv1 J1].
    left.
    exists 
         {|
         CurSystem := s;
         CurTargetData := (los, nts);
         CurProducts := ps;
         ECS := {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_select i0 v t v0 v1 :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := (if isGVZero (los, nts) gv 
                           then updateAddAL _ lc i0 gv1 
                           else updateAddAL _ lc i0 gv0);
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M |}.
     exists trace_nil. eauto.

  SCase "call". 
    assert (exists gvs, params2GVs (los, nts) p lc gl = Some gvs) as G.
      eapply params2GVs_isnt_stuck; eauto. 
        exists nil. auto.
    destruct G as [gvs G].
    remember (lookupFdefViaGV (los, nts) ps gl lc fs v) as Hlk. 
    destruct Hlk as [f' |].
    SSCase "internal call".
    destruct f' as [[fa rt fid la va] lb].
    assert (J:=HeqHlk).
    symmetry in HeqHlk.
    apply lookupFdefViaGV_inv in HeqHlk; auto.
    eapply wf_system__wf_fdef in HeqHlk; eauto.
    assert (Hinit := HeqHlk).
    apply initLocal__total with (gvs2:=gvs) in Hinit; auto.
    destruct Hinit as [lc2 Hinit].
    inv HeqHlk. destruct block5 as [l5 ps5 cs5 tmn5].
    left.
    exists 
         {|
         CurSystem := s;
         CurTargetData := (los, nts);
         CurProducts := ps;
         ECS :=(mkEC (fdef_intro (fheader_intro fa rt fid 
                       (map_list_typ_attributes_id
                         (fun (typ_ : typ) (attributes_ : attributes) (id_ : id) 
                         => (typ_, attributes_, id_)) typ_attributes_id_list)
                        va) lb) 
                       (block_intro l5 ps5 cs5 tmn5) cs5 tmn5 lc2
                       nil)::
               {|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_call i0 n c t v p :: cs) tmn;
                CurCmds := insn_call i0 n c t v p :: cs;
                Terminator := tmn;
                Locals := lc;
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := M |}.
    exists trace_nil.
    eauto.     

    remember (lookupExFdecViaGV (los, nts) ps gl lc fs v) as Helk. 
    destruct Helk as [f' |].
    SSCase "external call".
    destruct f' as [[fa rt fid la va]].
    remember (callExternalFunction M fid gvs) as R.
      destruct R as [[oresult Mem']|].
      remember (exCallUpdateLocals (los,nts) t n i0 oresult lc) as R'.
      destruct R' as [lc' |].
        left.
        exists 
         {|
         CurSystem := s;
         CurTargetData := (los, nts);
         CurProducts := ps;
         ECS :={|
                CurFunction := f;
                CurBB := block_intro l1 ps1
                           (cs1 ++ insn_call i0 n c t v p :: cs) tmn;
                CurCmds := cs;
                Terminator := tmn;
                Locals := lc';
                Allocas := als |} :: ecs;
         Globals := gl;
         FunTable := fs;
         Mem := Mem' |}.
        exists trace_nil.
        eauto.     

        right.
        unfold undefined_state.
        right. rewrite <- HeqHlk. rewrite <- HeqHelk. rewrite G. 
        rewrite <- HeqR0.
        rewrite <- HeqR'. undefbehave.

      right.
      unfold undefined_state.
      right. rewrite <- HeqHlk. rewrite <- HeqHelk. rewrite G.
      rewrite <- HeqR0. undefbehave.

    SSCase "stuck".
      right.
      unfold undefined_state.
      right. rewrite <- HeqHlk. rewrite <- HeqHelk. undefbehave.
Qed.


(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)
