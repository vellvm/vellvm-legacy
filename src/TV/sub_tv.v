Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa".
Add LoadPath "../ssa/compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import ssa_def.
Require Import ssa_lib.
Require Import List.
Require Import targetdata.
Require Import monad.
Require Import Arith.
Require Import Metatheory.
Require Import ssa_mem.
Require Import genericvalues.
Require Import ssa_dynamic.
Require Import opsem_pp.
Require Import trace.
Require Import symexe_def.
Require Import symexe_lib.
Require Import symexe_complete.
Require Import symexe_sound.
Require Import seop_llvmop.
Require Import assoclist.
Require Import ssa_props.
Require Import eq_tv_dec.
Require Import sub_tv_dec.
Require Import Coq.Bool.Sumbool.

Export SimpleSE.

Definition tv_cmds (nbs1 nbs2 : list nbranch) :=
sumbool2bool _ _ (sstate_sub_dec (se_cmds sstate_init nbs1) (se_cmds sstate_init nbs2)
                    (se_cmds_init_uniq nbs1)).

(* Realized to check if two function names are matched. For example,
 * in Softbound, 'test' in the original program matches 'softbound_test'.
*)
Axiom rename_fid : id -> id.

Definition tv_fid (fid1 fid2:id) := 
  sumbool2bool _ _ (id_dec (rename_fid fid1) fid2).

Axiom tv_fid_injective1 : forall fid1 fid2 fid1' fid2',
  fid1 = fid2 -> tv_fid fid1 fid1' -> tv_fid fid2 fid2' -> fid1' = fid2'.

Axiom tv_fid_injective2 : forall fid1 fid2 fid1' fid2',
  fid1 <> fid2 -> tv_fid fid1 fid1' -> tv_fid fid2 fid2' -> fid1' <> fid2'.

(* Here, we check which function to call conservatively. In practice, a v1
 * is a function pointer, we should look up the function name from the 
 * FunTable. Since the LLVM IR takes function names as function pointers,
 * if a program does not assign them to be other variables, they should
 * be the same. *)
Definition tv_scall (c1 c2:scall) :=
  let '(stmn_call rid1 nr1 tailc1 t1 v1 sts1) := c1 in
  let '(stmn_call rid2 nr2 tailc2 t2 v2 sts2) := c2 in
  (sumbool2bool _ _ (id_dec rid1 rid1)) &&
  (sumbool2bool _ _ (noret_dec nr1 nr2)) &&
  (sumbool2bool _ _ (tailc_dec tailc1 tailc2)) &&
  (sumbool2bool _ _ (typ_dec t1 t2)) && 
  (sumbool2bool _ _ (prefix_dec _ typ_sterm_dec sts1 sts2)) &&
  match (v1, v2) with
  | (value_const (const_gid _ fid1), value_const (const_gid _ fid2)) => 
      tv_fid fid1 fid2
  | (v1, v2) => sumbool2bool _ _ (value_dec v1 v2)
  end.

Definition tv_subblock (sb1 sb2:subblock) :=
match (sb1, sb2) with
| (mkSB nbs1 call1 iscall1, mkSB nbs2 call2 iscall2) =>
  let st1 := se_cmds sstate_init nbs1 in
  let st2 := se_cmds sstate_init nbs2 in
  let cl1 := se_call st1 call1 iscall1 in
  let cl2 := se_call st2 call2 iscall2 in
   (sumbool2bool _ _ (sstate_sub_dec st1 st2 (se_cmds_init_uniq nbs1))) &&
   tv_scall cl1 cl2
end.

Fixpoint tv_subblocks (sbs1 sbs2:list subblock) :=
match (sbs1, sbs2) with
| (nil, nil) => true
| (sb1::sbs1', sb2::sbs2') => 
   (tv_subblock sb1 sb2) && (tv_subblocks sbs1' sbs2')
| _ => false
end.

Fixpoint tv_phinodes (ps1 ps2:phinodes) :=
match (ps1, ps2) with
| (nil, nil) => true
| (p1::ps1', p2::ps2') => 
    sumbool2bool _ _ (phinode_dec p1 p2) && tv_phinodes ps1' ps2'
| _ => false
end.

Definition tv_block (b1 b2:block) :=
match (b1, b2) with
| (block_intro l1 ps1 cs1 tmn1, block_intro l2 ps2 cs2 tmn2) =>
  match (cmds2sbs cs1, cmds2sbs cs2) with
  | ((sbs1, nbs1), (sbs2, nbs2)) =>
    sumbool2bool _ _ (eq_atom_dec l1 l2) &&
    tv_phinodes ps1 ps2 &&
    tv_subblocks sbs1 sbs2 &&
    tv_cmds nbs1 nbs2 &&
    sumbool2bool _ _ (terminator_dec tmn1 tmn2)
  end
end.

Fixpoint tv_blocks (bs1 bs2:blocks):=
match (bs1, bs2) with
| (nil, nil) => true
| (b1::bs1', b2::bs2') => tv_block b1 b2 && tv_blocks bs1' bs2'
| _ => false
end.

Definition tv_fheader (f1 f2:fheader) := 
  let '(fheader_intro t1 fid1 a1) := f1 in
  let '(fheader_intro t2 fid2 a2) := f2 in
  (sumbool2bool _ _ (typ_dec t1 t2)) &&
  tv_fid fid1 fid2 &&
  (sumbool2bool _ _ (prefix_dec _ arg_dec a1 a2)).

Definition tv_fdef (f1 f2:fdef) :=
match (f1, f2) with
| (fdef_intro fh1 lb1, fdef_intro fh2 lb2) =>
  tv_fheader fh1 fh2 && tv_blocks lb1 lb2
end.

Definition tv_fdec (f1 f2:fdec) :=
match (f1, f2) with
| (fdec_intro fh1, fdec_intro fh2) => tv_fheader fh1 fh2
end.

Fixpoint lookupGvarViaIDFromProducts (lp:products) (i:id) : option gvar :=
match lp with
| nil => None
| (product_gvar gv)::lp' => 
    if (eq_dec (getGvarID gv) i) then Some gv
    else lookupGvarViaIDFromProducts lp' i
| _::lp' => lookupGvarViaIDFromProducts lp' i
end.

Definition products_sub (Ps1 Ps2:products) := forall id1, 
  In id1 (getProductsIDs Ps1) ->
  (forall fdec1,
    lookupFdecViaIDFromProducts Ps1 id1 = Some fdec1 ->
    exists fdec2,
      lookupFdecViaIDFromProducts Ps2 (rename_fid id1) = Some fdec2 /\ 
      tv_fdec fdec1 fdec2 = true)
  /\
  (forall fdef1,
    lookupFdefViaIDFromProducts Ps1 id1 = Some fdef1 ->
    exists fdef2,
      lookupFdefViaIDFromProducts Ps2 (rename_fid id1) = Some fdef2 /\ 
      tv_fdef fdef1 fdef2 = true)
  /\
  (forall gv1,
    lookupGvarViaIDFromProducts Ps1 id1 = Some gv1 ->
    exists gv2,
      lookupGvarViaIDFromProducts Ps2 id1 = Some gv2 /\ 
      sumbool2bool _ _ (gvar_dec gv1 gv2) = true).

(*
Lemma lookupAL_app1 : forall X (lc1:list (atom*X)) lc2 i,
  i `in` dom lc1 ->
  lookupAL X lc1 i = lookupAL X (lc1++lc2) i.
Proof.
  induction lc1; intros lc2 i Hi_in_lc1.
    fsetdec.
    destruct a as (id, elt); simpl in *.
    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) i id); auto.
      apply IHlc1. fsetdec.
Qed.    

Lemma lookupAL_app2 : forall X lc1 (lc2:list (atom*X)) i,
  i `notin` dom lc1 ->
  lookupAL X lc2 i = lookupAL X (lc1++lc2) i.
Proof.
  induction lc1; intros lc2 i Hi_notin_lc1; auto.
    destruct a as (id, elt); simpl in *.
    destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) i id); subst; eauto.
      fsetdec.
Qed.    
*)

Lemma products_sub_app1 : forall Ps1 Ps2 Ps,
  products_sub Ps1 Ps -> 
  products_sub Ps2 Ps ->
  products_sub (Ps1++Ps2) Ps.
Proof.
  intros Ps1 Ps2 Ps HPs1_sub_Ps HPs2_sub_Ps.
  intros i i_in_Ps12.
(*
  simpl_env in i_in_lc12.
  apply in_dom_app_inv in i_in_lc12.
  assert (i `in`  dom lc1 \/ i `notin` dom lc1) as i_in_lc1_dec. fsetdec.
  destruct i_in_lc1_dec as [i_in_lc1 | i_notin_lc1].
    rewrite <- Hlc1_sub_lc; auto.
    rewrite <- lookupAL_app1; auto.

    destruct i_in_lc12 as [i_in_lc1 | i_in_lc2].
      fsetdec.
      rewrite <- lookupAL_app2; auto.
*)
Admitted.

(*
Lemma lookupALs_tail : forall X l2b l2b' l0,
  l0 `notin` dom l2b ->
  lookupAL X (l2b++l2b') l0 = lookupAL _ l2b' l0.
Proof.
  intros.
  induction l2b; auto.
    destruct a. simpl in *.
    destruct (@eq_dec atom (@EqDec_eq_of_EqDec atom EqDec_atom) l0 a); subst; auto.
      fsetdec.
Qed.
*)

Lemma products_sub_app2 : forall Ps1 Ps2 Ps,
  products_sub Ps1 Ps -> 
  NoDup (getProductsIDs (Ps1++Ps2)) ->
  ~ products_sub Ps2 Ps ->
  ~ products_sub (Ps1++Ps2) Ps.
Admitted.
(*
Proof.
  intros X lc1 lc2 lc Hlc1_sub_lc Hdisj Hlc2_nsub_lc Hlc12_sub_lc.
  apply Hlc2_nsub_lc.
  intros i i_in_lc2.
    assert (i `notin` dom lc1) as i_notin_lc1. solve_uniq.
    assert (i `in` dom (lc1++lc2)) as i_in_lc12. simpl_env. fsetdec.
    apply Hlc12_sub_lc in i_in_lc12.
    erewrite lookupALs_tail in i_in_lc12; eauto.
Qed.
*)

Lemma products_sub_dec: forall Ps1 Ps2, 
  NoDup (getProductsIDs Ps1) ->
  {products_sub Ps1 Ps2} + {~products_sub Ps1 Ps2}.
Proof.
  induction Ps1; intros Ps2 Huniq.
    left. intros id1 Hindom. 
    inversion Hindom.

    simpl in Huniq.
    rewrite_env (nil ++ getProductID a :: getProductsIDs Ps1) in Huniq.
    assert (Hnotindom:=Huniq).
    apply NoDup_remove_2 in Hnotindom.
    assert (Huniq':=Huniq).
    apply NoDup_remove_1 in Huniq'.
    simpl_env in *.
    destruct a as [g1 | f1 | f1].
    Case "gvar".
      remember (lookupGvarViaIDFromProducts Ps2 (getGvarID g1)) as Lookup.
      destruct Lookup as [g2 | ].
      SCase "gid in Ps2".
        destruct (gvar_dec g1 g2); subst.
        SSCase "g1 = g2".
          assert (products_sub [product_gvar g2] Ps2) as Hg2_sub_Ps2.
            intros i Hi_in_dom. simpl. 
            repeat split; try solve [intros a Hlookup; inversion Hlookup].
            intros gv1 Hlookup.
            destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) (getGvarID g2) i); inversion Hlookup; subst.
              exists gv1. split; auto.
              destruct (gvar_dec gv1 gv1); simpl; auto.
          destruct (@IHPs1 Ps2 Huniq') as [HPs1_sub_Ps2 | HPs1_nsub_Ps2].
            left. apply products_sub_app1; auto.
            right. apply products_sub_app2; auto.
          
        SSCase "g1 <> g2".
          right. intro J.
          assert (In (getGvarID g1) (getProductsIDs ([product_gvar g1]++Ps1))) 
            as Hindom. 
            simpl. auto.
          assert (H:=@J (getGvarID g1) Hindom). simpl in H.
          destruct H as [_ [_ H3]].
          destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) (getGvarID g1) (getGvarID g1)) as [e | n']; try solve [contradict n'; auto].
          destruct (@H3 g1) as [gv2 [J1 J2]]; auto.
          rewrite <- HeqLookup in J1. inversion J1; subst.
          destruct (gvar_dec g1 gv2); subst; auto.
            simpl in J2. inversion J2.

      SCase "gid notin Ps2".
        right. intro J.
        assert (In (getGvarID g1) (getProductsIDs ([product_gvar g1]++Ps1))) 
          as Hindom. 
          simpl. auto.
        assert (H:=@J (getGvarID g1) Hindom). simpl in H.
        destruct H as [H1 [H2 H3]].
        destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) (getGvarID g1) (getGvarID g1)) as [e | n']; try solve [contradict n'; auto].
        destruct (@H3 g1) as [gv2 [J1 J2]]; auto.       
        rewrite <- HeqLookup in J1. inversion J1.
        
    Case "fdec".
      remember (lookupFdecViaIDFromProducts Ps2 (rename_fid (getFdecID f1))) as Lookup.
      destruct Lookup as [f2 | ].
      SCase "fid in Ps2".
        remember (tv_fdec f1 f2) as R.
        destruct R; subst.
        SSCase "f1 = f2".
          assert (products_sub [product_fdec f1] Ps2) as Hf2_sub_Ps2.
            intros i Hi_in_dom. simpl. 
            repeat split; try solve [intros a Hlookup; inversion Hlookup].
            intros fdec1 Hlookup.
            destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) (getFdecID f1) i); inversion Hlookup; subst.
              exists f2. split; auto.
          destruct (@IHPs1 Ps2 Huniq') as [HPs1_sub_Ps2 | HPs1_nsub_Ps2].
            left. apply products_sub_app1; auto.
            right. apply products_sub_app2; auto.
          
        SSCase "f1 <> f2".
          right. intro J.
          assert (In (getFdecID f1) (getProductsIDs ([product_fdec f1]++Ps1))) 
            as Hindom. 
            simpl. auto.
          assert (H:=@J (getFdecID f1) Hindom). simpl in H.
          destruct H as [H1 _].
          destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) (getFdecID f1) (getFdecID f1)) as [e | n']; try solve [contradict n'; auto].
          destruct (@H1 f1) as [fdec2 [J1 J2]]; auto.
          rewrite <- HeqLookup in J1. inversion J1; subst.
          rewrite J2 in HeqR. inversion HeqR.

      SCase "fid notin Ps2".
        right. intro J.
        assert (In (getFdecID f1) (getProductsIDs ([product_fdec f1]++Ps1))) 
          as Hindom. 
          simpl. auto.
        assert (H:=@J (getFdecID f1) Hindom). simpl in H.
        destruct H as [H1 [H2 H3]].
        destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) (getFdecID f1) (getFdecID f1)) as [e | n']; try solve [contradict n'; auto].
        destruct (@H1 f1) as [fdec2 [J1 J2]]; auto.       
        rewrite <- HeqLookup in J1. inversion J1.

    Case "fdef".
      remember (lookupFdefViaIDFromProducts Ps2 (rename_fid (getFdefID f1))) as Lookup.
      destruct Lookup as [f2 | ].
      SCase "fid in Ps2".
        remember (tv_fdef f1 f2) as R.
        destruct R; subst.
        SSCase "f1 = f2".
          assert (products_sub [product_fdef f1] Ps2) as Hf2_sub_Ps2.
            intros i Hi_in_dom. simpl. 
            repeat split; try solve [intros a Hlookup; inversion Hlookup].
            intros fdef1 Hlookup.
            destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) (getFdefID f1) i); inversion Hlookup; subst.
              exists f2. split; auto.
          destruct (@IHPs1 Ps2 Huniq') as [HPs1_sub_Ps2 | HPs1_nsub_Ps2].
            left. apply products_sub_app1; auto.
            right. apply products_sub_app2; auto.
          
        SSCase "f1 <> f2".
          right. intro J.
          assert (In (getFdefID f1) (getProductsIDs ([product_fdef f1]++Ps1))) 
            as Hindom. 
            simpl. auto.
          assert (H:=@J (getFdefID f1) Hindom). simpl in H.
          destruct H as [_ [H2 _]].
          destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) (getFdefID f1) (getFdefID f1)) as [e | n']; try solve [contradict n'; auto].
          destruct (@H2 f1) as [fdef2 [J1 J2]]; auto.
          rewrite <- HeqLookup in J1. inversion J1; subst.
          rewrite J2 in HeqR. inversion HeqR.

      SCase "fid notin Ps2".
        right. intro J.
        assert (In (getFdefID f1) (getProductsIDs ([product_fdef f1]++Ps1))) 
          as Hindom. 
          simpl. auto.
        assert (H:=@J (getFdefID f1) Hindom). simpl in H.
        destruct H as [_ [H2 _]].
        destruct (@eq_dec id (EqDec_eq_of_EqDec id EqDec_atom) (getFdefID f1) (getFdefID f1)) as [e | n']; try solve [contradict n'; auto].
        destruct (@H2 f1) as [fdec2 [J1 J2]]; auto.       
        rewrite <- HeqLookup in J1. inversion J1.
Qed.

Lemma tv_products: forall (Ps1 Ps2:products), NoDup (getProductsIDs Ps1) -> bool.
Proof.
  intros Ps1 Ps2 Huniq.
  apply (sumbool2bool _ _ (products_sub_dec Ps1 Ps2 Huniq)).
Defined.

Lemma tv_module : forall (m1 m2:module), uniqModule m1 -> bool.
Proof.
  intros m1 m2 Huniq.
  destruct m1 as [los1 nts1 Ps1].
  destruct m2 as [los2 nts2 Ps2].
  destruct Huniq as [_ [_ Huniq]].
  apply (sumbool2bool _ _ (layouts_dec los1 los2) &&
         sumbool2bool _ _ (namedts_dec nts1 nts2) &&
         tv_products Ps1 Ps2 Huniq).
Defined.

Lemma tv_system : forall (S1 S2:system), uniqSystem S1 -> bool.
Proof.
  induction S1 as [ | m1 S1]; intros S2 Huniq.
    destruct S2.
      apply true.
      apply false.

    destruct S2 as [ | m2 S2].
      apply false.

      assert (uniqModule m1) as Huniq1.
        inversion Huniq; auto.
      assert (uniqSystem S1) as Huniq2.
        inversion Huniq; auto.
      apply (tv_module m1 m2 Huniq1 && IHS1 S2 Huniq2).
Defined.

Ltac sumbool_simpl :=
  repeat
  match goal with
  | [ H:sumbool2bool _ _ _ = true |- _ ] => apply sumbool2bool_true in H
  | [ H:is_true(sumbool2bool _ _ _) |- _ ] => apply sumbool2bool_true in H
  | [ H:tv_cmds _ _ = true |- _ ] => unfold is_true in H; apply sumbool2bool_true in H
  | [ H:is_true(tv_cmds _ _) |- _ ] => unfold is_true in H; apply sumbool2bool_true in H
  end.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)
