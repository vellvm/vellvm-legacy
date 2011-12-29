Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../Vellvm".
Add LoadPath "../../../theory/metatheory_8.3".
Add LoadPath "../SoftBound".
Require Import vellvm.
Require Import Kildall.
Require Import ListSet.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import Maps.
Require Import opsem_props.
Require Import promotable_props.
Require Import primitives.
Require Import palloca_props.
Require Import memory_props.
Require Import sb_msim.
Require Import sb_ds_gv_inject.

Definition fdef_simulation (pinfo: PhiInfo) f1 f2 : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then 
    remove_fdef (PI_id pinfo) f1 = f2
  else f1 = f2.

Definition cmds_simulation (pinfo: PhiInfo) (f1:fdef) cs1 cs2 : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then 
    remove_cmds (PI_id pinfo) cs1 = cs2
  else cs1 = cs2.

Definition block_simulation (pinfo: PhiInfo) (f1:fdef) b1 b2 : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then 
    remove_block (PI_id pinfo) b1 = b2
  else b1 = b2.

Definition products_simulation (pinfo: PhiInfo) Ps1 Ps2 : Prop :=
List.Forall2 
  (fun P1 P2 =>
   match P1, P2 with
   | product_fdef f1, product_fdef f2 => fdef_simulation pinfo f1 f2
   | _, _ => P1 = P2
   end) Ps1 Ps2.

Definition system_simulation (pinfo: PhiInfo) S1 S2 : Prop :=
List.Forall2 
  (fun M1 M2 =>
   match M1, M2 with
   | module_intro los1 nts1 Ps1, module_intro los2 nts2 Ps2 =>
       los1 = los2 /\ nts1 = nts2 /\ 
       products_simulation pinfo Ps1 Ps1
   end) S1 S2.

Definition is_alloca_in_EC (pinfo: PhiInfo) F1 (lc1:@Opsem.GVsMap DGVs) 
  (blk1: mblock) : bool := 
  if (fdef_dec (PI_f pinfo) F1) then 
    match lookupAL _ lc1 (PI_id pinfo) with
    | Some ((Vptr b _,_)::nil) =>
        if (Z_eq_dec b blk1) then true
        else false
    | _ => false
    end 
  else false.

Definition als_blk_simulation (pinfo: PhiInfo) (mi:MoreMem.meminj) F1 
  (lc1:@Opsem.GVsMap DGVs) (blk1 blk2: mblock) : Prop := 
  if (is_alloca_in_EC pinfo F1 lc1 blk1) then mi blk1 = None
  else mi blk1 = Some (blk2, 0).

Fixpoint als_simulation (pinfo: PhiInfo) (mi:MoreMem.meminj) F1 lc1
  (als1 als2:list mblock) : Prop :=
  match (als1, als2) with
  | (nil, nil) => True
  | (b1::als1', _) => 
      if (is_alloca_in_EC pinfo F1 lc1 b1) then 
        mi b1 = None /\ als_simulation pinfo mi F1 lc1 als1' als2
      else 
        match als2 with 
        | b2::als2' => 
           mi b1 = Some (b2, 0) /\ als_simulation pinfo mi F1 lc1 als1' als2'
        | _ => False
        end
  | _ => False
  end.

Definition reg_simulation (pinfo: PhiInfo) (mi:MoreMem.meminj) (F1:fdef) 
  (lc1 lc2:@Opsem.GVsMap DGVs) : Prop :=
  if (fdef_dec (PI_f pinfo) F1) then 
    forall i0,
      if (id_dec (PI_id pinfo) i0) then True
      else
        forall gv1 gv2,
          lookupAL _ lc1 i0 = Some gv1 -> 
          lookupAL _ lc2 i0 = Some gv2 -> 
          gv_inject mi gv1 gv2
  else
    forall i0 gv1 gv2,
      lookupAL _ lc1 i0 = Some gv1 -> 
      lookupAL _ lc2 i0 = Some gv2 -> 
      gv_inject mi gv1 gv2.

Definition EC_simulation (pinfo: PhiInfo) (mi:MoreMem.meminj) 
  (EC1 EC2:@Opsem.ExecutionContext DGVs) : Prop :=
  match (EC1, EC2) with
  | (Opsem.mkEC f1 b1 cs1 tmn1 lc1 als1, 
     Opsem.mkEC f2 b2 cs2 tmn2 lc2 als2) =>
       fdef_simulation pinfo f1 f2 /\
       tmn1 = tmn2 /\
       als_simulation pinfo mi f1 lc1 als1 als2 /\
       block_simulation pinfo f1 b1 b2 /\
       (exists l1, exists ps1, exists cs11, 
         b1 = block_intro l1 ps1 (cs11++cs1) tmn1)
         /\
       (exists l2, exists ps2, exists cs21,
         b2 = block_intro l2 ps2 (cs21++cs2) tmn2) /\
       reg_simulation pinfo mi f1 lc1 lc2 /\
       cmds_simulation pinfo f1 cs1 cs2
  end.

Fixpoint ECs_simulation (pinfo: PhiInfo) mi (ECs1 ECs2:@Opsem.ECStack DGVs) 
  : Prop :=
match ECs1, ECs2 with
| nil, nil => True
| EC1::ECs1', EC2::ECs2' => 
    EC_simulation pinfo mi EC1 EC2 /\ ECs_simulation pinfo mi ECs1' ECs2'
| _, _ => False
end.

Definition isnt_alloca_in_ECs (pinfo:PhiInfo) (ecs:list Opsem.ExecutionContext) 
  (blk:mblock) : Prop :=
  forall ec0 (Hin: In ec0 ecs), 
    is_alloca_in_EC pinfo (Opsem.CurFunction ec0) (Opsem.Locals ec0) blk = false.

Definition Mem_simulation (pinfo:PhiInfo) mgb (mi:MoreMem.meminj)
  (ecs:list Opsem.ExecutionContext) Mem1 Mem2 : Prop :=
MoreMem.mem_inj mi Mem1 Mem2 /\
(forall blk, 
   (isnt_alloca_in_ECs pinfo ecs blk -> mi blk <> None) /\
   ~ isnt_alloca_in_ECs pinfo ecs blk -> mi blk = None) /\
wf_sb_mi mgb mi Mem1 Mem2.

(* Copied from sb_ds_sim *)
Definition ftable_simulation mi fs1 fs2 : Prop :=
  forall fv1 fv2, gv_inject mi fv1 fv2 ->
    OpsemAux.lookupFdefViaGVFromFunTable fs1 fv1 = 
    OpsemAux.lookupFdefViaGVFromFunTable fs2 fv2.

Definition State_simulation (pinfo: PhiInfo) mgb (mi:MoreMem.meminj)
  (Cfg1:OpsemAux.Config) (St1:Opsem.State) 
  (Cfg2:OpsemAux.Config) (St2:Opsem.State) : Prop :=
let '(OpsemAux.mkCfg S1 TD1 Ps1 gl1 fs1) := Cfg1 in
let '(OpsemAux.mkCfg S2 TD2 Ps2 gl2 fs2) := Cfg2 in
match (St1, St2) with
| (Opsem.mkState ECs1 M1, Opsem.mkState ECs2 M2) =>
    TD1 = TD2 /\ 
    products_simulation pinfo Ps1 Ps2 /\
    ECs_simulation pinfo mi ECs1 ECs2 /\
    gl1 = gl2 /\ ftable_simulation mi fs1 fs2 /\ 
    Mem_simulation pinfo mgb mi ECs1 M1 M2
end.

Definition removable_State (pinfo: PhiInfo) (St:@Opsem.State DGVs) : Prop :=
match St with
| Opsem.mkState
    (Opsem.mkEC f b (c :: cs) tmn lc als::_) _ => 
    if (fdef_dec (PI_f pinfo) f) then 
      if (id_dec (PI_id pinfo) (getCmdLoc c)) then True else False
    else False
| _ => False
end.

Lemma removable_State_dec : forall pinfo St,
  removable_State pinfo St \/ ~ removable_State pinfo St.
Proof.
  destruct St. 
  destruct ECS as [|[]]; auto.
  destruct CurCmds; auto.
  simpl.
  destruct (fdef_dec (PI_f pinfo) CurFunction); auto.
  destruct (id_dec (PI_id pinfo) (getCmdLoc c)); auto.
Qed.

Lemma cmds_simulation_elim_cons_inv: forall (pinfo : PhiInfo) c (cs1 : list cmd) 
  (cs2 : cmds) (Heq : PI_id pinfo = getCmdLoc c)
  (Hcssim2 : cmds_simulation pinfo (PI_f pinfo) (c :: cs1) cs2),
  cmds_simulation pinfo (PI_f pinfo) cs1 cs2.
Proof.
  intros.
  unfold cmds_simulation in *.
  destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
  simpl in *. rewrite Heq in Hcssim2.
  destruct (id_dec (getCmdLoc c) (getCmdLoc c)); simpl in *; try congruence.
Qed.

(* copied from id_rhs_val.v *)
Ltac uniq_result :=
repeat dgvs_instantiate_inv;
repeat match goal with
| H1 : ?f ?a ?b ?c ?d = _,
  H2 : ?f ?a ?b ?c ?d = _ |- _ =>
  rewrite H1 in H2; inv H2
| H1 : ?f ?a ?b ?c = _,
  H2 : ?f ?a ?b ?c = _ |- _ =>
  rewrite H1 in H2; inv H2
| H1 : ?f ?a ?b = _,
  H2 : ?f ?a ?b = _ |- _ =>
  rewrite H1 in H2; inv H2
| H1 : _ @ _ |- _ => inv H1
end.

Lemma cmds_simulation_nil_inv: forall pinfo f1 cs,
  cmds_simulation pinfo f1 nil cs -> cs = nil.
Proof.
  unfold cmds_simulation. simpl.
  intros. destruct (fdef_dec (PI_f pinfo) f1); auto.
Qed.

Lemma cmds_simulation_nelim_cons_inv: forall pinfo F c cs2 cs',
  cmds_simulation pinfo F (c :: cs2) cs' ->
  PI_f pinfo <> F \/ PI_id pinfo <> getCmdLoc c ->
  exists cs2', 
    cs' = c :: cs2' /\ cmds_simulation pinfo F cs2 cs2'.
Proof.  
  intros.
  unfold cmds_simulation in *.
  destruct (fdef_dec (PI_f pinfo) F); subst; simpl; eauto.
  destruct (id_dec (getCmdLoc c) (PI_id pinfo)); subst; simpl; eauto.
  rewrite e in H0.
  destruct H0; congruence.
Qed.

(* copied from las.v *)
Ltac wfCall_inv :=
match goal with
| Heq3 : exists _,
           exists _,
             exists _,
               ?B = block_intro _ _ _ _,
  HBinF1 : blockInFdefB ?B ?F = true,
  HwfCall : OpsemPP.wf_call 
              {| 
              Opsem.CurFunction := ?F;
              Opsem.CurBB := ?B;
              Opsem.CurCmds := nil;
              Opsem.Terminator := _;
              Opsem.Locals := _;
              Opsem.Allocas := _ |} 
              ({|
               Opsem.CurFunction := _;
               Opsem.CurBB := _;
               Opsem.CurCmds := ?c' :: _;
               Opsem.Terminator := _;
               Opsem.Locals := _;
               Opsem.Allocas := _ |}  :: _) |- _ =>
  let cs3 := fresh "cs3" in
  destruct Heq3 as [l3 [ps3 [cs3 Heq3]]]; subst;
  assert (HBinF1':=HBinF1);
  apply HwfCall in HBinF1';
  destruct c'; tinv HBinF1'; clear HBinF1'
end.


Lemma fdef_sim__block_sim : forall pinfo f1 f2 b1 b2 l0,
  fdef_simulation pinfo f1 f2 ->
  lookupBlockViaLabelFromFdef f1 l0 = Some b1 ->
  lookupBlockViaLabelFromFdef f2 l0 = Some b2 ->
  block_simulation pinfo f1 b1 b2.
Admitted.

Definition phis_simulation (pinfo: PhiInfo) (f1:fdef) ps1 ps2 : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then remove_phinodes (PI_id pinfo) ps1 = ps2
  else ps1 = ps2.

Lemma block_simulation_inv : forall pinfo F l1 ps1 cs1 tmn1 l2 ps2 cs2
  tmn2,
  block_simulation pinfo F (block_intro l1 ps1 cs1 tmn1)
    (block_intro l2 ps2 cs2 tmn2) ->
  l1 = l2 /\ phis_simulation pinfo F ps1 ps2 /\ 
  cmds_simulation pinfo F cs1 cs2 /\ tmn1 = tmn2.
Proof.
  intros.
  unfold block_simulation, cmds_simulation, phis_simulation in *.
  destruct (fdef_dec (PI_f pinfo) F); inv H; auto.
Qed.

(*
Lemma no_alias_head_tail_update : 
  forall pinfo ptr EC1 EC2 ECs
  (EQ: Opsem.CurFunction EC1 = Opsem.CurFunction EC2)
  (Hp: forall gvsa
   (Hlkup: lookupAL (GVsT DGVs) (Opsem.Locals EC2) (PI_id pinfo) = ret gvsa),
   lookupAL (GVsT DGVs) (Opsem.Locals EC1) (PI_id pinfo) = ret gvsa)
  (Hnalias: no_alias_head_tail pinfo ptr (EC1 :: ECs)),
  no_alias_head_tail pinfo ptr (EC2 :: ECs).
Proof.
  intros.
  unfold no_alias_head_tail in *.
  intros.
  simpl in Hin.
  destruct Hin as [Hin | Hin]; subst.
    assert (no_alias_head_in_tail pinfo ptr EC1) as J. 
      apply Hnalias; simpl; auto.
    clear Hnalias.
    unfold no_alias_head_in_tail in *. simpl in *. intros. 
    rewrite Heq in EQ.
    apply J; auto.

    apply Hnalias; simpl; auto.
Qed.

Lemma switchToNewBasicBlock_sim : forall TD l1 l2 ps cs1 cs2 tmn1 tmn2 B1 B2 
  gl lc lc1 lc2 F pinfo
  (H23 : @Opsem.switchToNewBasicBlock DGVs TD
          (block_intro l1 ps cs1 tmn1) B1 gl lc = 
         ret lc1)
  (Hbsim2 : block_simulation pinfo F B1 B2)
  (H2 : Opsem.switchToNewBasicBlock TD
         (block_intro l2 ps cs2 tmn2) B2 gl lc = 
        ret lc2), lc1 = lc2.
Admitted.

Lemma mem_simulation_update_locals : 
  forall pinfo TD EC1 EC2 ECs M1 M2
  (EQ: Opsem.CurFunction EC1 = Opsem.CurFunction EC2)
  (Hp: forall gvsa
   (Hlkup: lookupAL (GVsT DGVs) (Opsem.Locals EC1) (PI_id pinfo) = ret gvsa),
   lookupAL (GVsT DGVs) (Opsem.Locals EC2) (PI_id pinfo) = ret gvsa)
  (Hmsim: Mem_simulation pinfo TD (EC1 :: ECs) M1 M2),
  Mem_simulation pinfo TD (EC2 :: ECs) M1 M2.
Proof.
  intros.
  destruct Hmsim as [Hmsim1 Hmsim2].
  split; auto.
    intros.
    eapply Hmsim2 with (ptr:=ptr)(ty:=ty)(al:=al); eauto.
    eapply no_alias_head_tail_update in Hnalias; eauto; simpl; auto.
Qed.

Lemma mstore_palloca_Mem_simulation: forall TD M1 mp2 gv1 a M1' pinfo lc2 gl2
  B1 cs1 tmn2 als2 ECs1 M2 i0 t v
  (H23: mstore TD M1 mp2 t gv1 a = ret M1')
  (H20: @Opsem.getOperandValue DGVs TD (value_id (PI_id pinfo)) lc2 gl2 =
          ret mp2)
  (Hmsim: Mem_simulation pinfo TD
            ({|
             Opsem.CurFunction := PI_f pinfo;
             Opsem.CurBB := B1;
             Opsem.CurCmds := insn_store i0 t v (value_id (PI_id pinfo)) a
                              :: cs1;
             Opsem.Terminator := tmn2;
             Opsem.Locals := lc2;
             Opsem.Allocas := als2 |} :: ECs1) M1 M2),
  Mem_simulation pinfo TD
            ({|
             Opsem.CurFunction := PI_f pinfo;
             Opsem.CurBB := B1;
             Opsem.CurCmds := cs1;
             Opsem.Terminator := tmn2;
             Opsem.Locals := lc2;
             Opsem.Allocas := als2 |} :: ECs1) M1' M2.
Proof.
  intros.
  destruct Hmsim as [Hmsim1 Hmsim2].
  split.
    apply MemProps.nextblock_mstore in H23.
    rewrite <- H23. auto.

    intros. 
    eapply Hmsim2; eauto using no_alias_head_tail_irrel.
    eapply MemProps.mstore_preserves_mload_inv'; eauto.
    assert (no_alias_head_in_tail pinfo ptr 
              {| Opsem.CurFunction := PI_f pinfo;
                 Opsem.CurBB := B1;
                 Opsem.CurCmds := cs1;
                 Opsem.Terminator := tmn2;
                 Opsem.Locals := lc2;
                 Opsem.Allocas := als2 |}) as J.
      apply Hnalias; simpl; auto.
    apply MemProps.no_alias_sym.
    unfold no_alias_head_in_tail in J; eauto.
Qed.

Ltac repeat_solve :=
  repeat (match goal with
          | |- Mem_simulation _ _ _ _ _ => idtac 
          | |- _ => split; eauto 2 using cmds_at_block_tail_next
          end).
*)

Lemma products_simulation__fdef_simulation : forall pinfo Ps1 Ps2 fid f1 f2,
  lookupFdefViaIDFromProducts Ps2 fid = Some f2 ->
  lookupFdefViaIDFromProducts Ps1 fid = Some f1 ->
  products_simulation pinfo Ps1 Ps2 ->
  fdef_simulation pinfo f1 f2.
Admitted.

Lemma lookupFdefViaPtr__simulation : forall pinfo Ps1 Ps2 fptr f1 f2 fs,
  OpsemAux.lookupFdefViaPtr Ps2 fs fptr = Some f2 ->
  products_simulation pinfo Ps1 Ps2 ->
  OpsemAux.lookupFdefViaPtr Ps1 fs fptr = Some f1 ->
  fdef_simulation pinfo f1 f2.
Proof.
  intros.
  unfold OpsemAux.lookupFdefViaPtr in *.
  remember (OpsemAux.lookupFdefViaGVFromFunTable fs fptr) as R2.
  destruct R2 as [fid|]; inv H1. simpl in H.
  eapply products_simulation__fdef_simulation in H0; eauto.
Qed.

Lemma fdef_simulation__entry_block_simulation: forall pinfo F1 F2 B1 B2,
  fdef_simulation pinfo F1 F2 ->
  getEntryBlock F1 = ret B1 ->
  getEntryBlock F2 = ret B2 ->
  block_simulation pinfo F1 B1 B2.
Admitted.

Lemma fdef_simulation_inv: forall pinfo fh1 fh2 bs1 bs2,
  fdef_simulation pinfo (fdef_intro fh1 bs1) (fdef_intro fh2 bs2) ->
  fh1 = fh2 /\ 
  List.Forall2 
    (fun b1 b2 => block_simulation pinfo (fdef_intro fh1 bs1) b1 b2) bs1 bs2.
Admitted.

Lemma lookupFdefViaPtr__simulation_l2r : forall pinfo Ps1 Ps2 fptr f1 fs,
  products_simulation pinfo Ps1 Ps2 ->
  OpsemAux.lookupFdefViaPtr Ps1 fs fptr = Some f1 ->
  exists f2, 
    OpsemAux.lookupFdefViaPtr Ps2 fs fptr = Some f2 /\
    fdef_simulation pinfo f1 f2.
Admitted.

Lemma lookupExFdecViaPtr__simulation_l2r : forall pinfo Ps1 Ps2 fptr f fs,
  products_simulation pinfo Ps1 Ps2 ->
  OpsemAux.lookupExFdecViaPtr Ps1 fs fptr = Some f ->
  OpsemAux.lookupExFdecViaPtr Ps2 fs fptr = Some f.
Admitted.
(*
Lemma no_alias_head_tail_cons_and: forall pinfo ptr EC ECs,
  no_alias_head_tail pinfo ptr (EC :: ECs) ->
  no_alias_head_in_tail pinfo ptr EC /\ no_alias_head_tail pinfo ptr ECs.
Proof.
  intros.
  unfold no_alias_head_tail in *.  
  split.
    apply H; simpl; auto.
    intros. apply H; simpl; auto.
Qed.
*)

Lemma callExternalFunction__Mem_simulation: forall pinfo mi St1 M1 M2 fid0 gvss0
  oresult1 M1' oresult2 M2' mgb,
  Mem_simulation pinfo mgb mi St1 M1 M2 ->
  OpsemAux.callExternalFunction M1 fid0 gvss0 = ret (oresult1, M1') ->
  OpsemAux.callExternalFunction M2 fid0 gvss0 = ret (oresult2, M2') ->
  oresult1 = oresult2 /\ 
  exists mi', 
    Mem_simulation pinfo mgb mi' St1 M1' M2' /\ Values.inject_incr mi mi'.
Admitted.
(*
Ltac dse_is_sim_common_case :=
match goal with
| Hcssim2: cmds_simulation _ _ _ _,
  Hop2: Opsem.sInsn _ _ _ _,
  Hmsim: Mem_simulation _ _ _ _ _ |- _ =>
  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl; auto;
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result;
  repeat_solve;
    eapply mem_simulation_update_locals in Hmsim; simpl; try solve [
      eauto |
      simpl; intros;
      match goal with
      | Hlkup : lookupAL _ ?lc ?id1 = Some ?gvsa |-
        lookupAL _ (updateAddAL _ ?lc _ _ ) ?id1 = Some ?gvsa => 
        admit  (* id <> palloca *)
      end]
end.
*)  

Lemma mem_simulation__palloca : forall mi TD Mem1 Mem2 tsz gn Mem1' mb B1
  v cs1 tmn1 als1 ECs1 pinfo maxb lc1
  (Hmsim : Mem_simulation pinfo maxb mi
            ({|
             Opsem.CurFunction := PI_f pinfo;
             Opsem.CurBB := B1;
             Opsem.CurCmds := insn_alloca (PI_id pinfo) 
                                (PI_typ pinfo) v (PI_align pinfo) :: cs1;
             Opsem.Terminator := tmn1;
             Opsem.Locals := lc1;
             Opsem.Allocas := als1 |} :: ECs1) Mem1 Mem2)
  (Hmlc: malloc TD Mem1 tsz gn (PI_align pinfo) = ret (Mem1', mb)),
  exists mi',
    Mem_simulation pinfo maxb mi'
            ({|
             Opsem.CurFunction := PI_f pinfo;
             Opsem.CurBB := B1;
             Opsem.CurCmds := cs1;
             Opsem.Terminator := tmn1;
             Opsem.Locals := 
               updateAddAL (GVsT DGVs) lc1 (PI_id pinfo)
                 ($ blk2GV TD mb # typ_pointer (PI_typ pinfo) $);
             Opsem.Allocas := mb :: als1 |} :: ECs1) Mem1' Mem2 /\
    Values.inject_incr mi mi' /\
    mi' mb = None /\
    (forall b, b <> mb -> mi b = mi' b).
Admitted.

Ltac repeat_solve :=
  repeat (match goal with
          | |- Mem_simulation _ _ _ _ _ _ => idtac 
          | |- _ => split; eauto 2 using cmds_at_block_tail_next
          end).

Lemma als_simulation_weaken_palloca: 
  forall mi' mb mi pinfo lc1 ofs mc
  (Hlkup : lookupAL _ lc1 (PI_id pinfo) = None)
  (Hmi1 : mi' mb = merror)
  (Hmi2 : forall b : mblock, b <> mb -> mi b = mi' b)
  als1 als2 
  (Hsim : als_simulation pinfo mi (PI_f pinfo) lc1 als1 als2)
  (Hfresh : forall al, In al als1 -> al <> mb),
  als_simulation pinfo mi' (PI_f pinfo)
    (updateAddAL _ lc1 (PI_id pinfo) ((Vptr mb ofs, mc) :: nil)) 
    als1 als2.
Proof.
  induction als1; simpl; intros; auto.
    unfold is_alloca_in_EC in *.
    rewrite Hlkup in Hsim.
    destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
    destruct (id_dec (PI_id pinfo) (PI_id pinfo)); try congruence.
    rewrite lookupAL_updateAddAL_eq.
    destruct (Z_eq_dec mb a); subst.
      assert (a <> a) as Hneq.
        apply Hfresh; auto.
      congruence.

      destruct als2; auto.
      destruct Hsim as [Hsim1 Hsim2].
      split.
        rewrite <- Hmi2; auto.
        apply IHals1; auto.
Qed.    

Lemma als_simulation_update_palloca: 
  forall mi' mb mi pinfo lc1 TD M1 tsz gn M1'
  (H21: malloc TD M1 tsz gn (PI_align pinfo) = Some (M1', mb))
  (Hlkup : lookupAL _ lc1 (PI_id pinfo) = None)
  (Hmi1 : mi' mb = merror)
  (Hmi2 : forall b : mblock, b <> mb -> mi b = mi' b) maxb
  als1 als2 (Hsim : als_simulation pinfo mi (PI_f pinfo) lc1 als1 als2) ECs1
  (Halsbd : forall al : Values.block,
            In al
              (als1 ++
               flat_map
                 (fun ec : @Opsem.ExecutionContext DGVs =>
                  let '{| Opsem.Allocas := als |} := ec in als) ECs1) ->
            maxb < al < Mem.nextblock M1),
  als_simulation pinfo mi' (PI_f pinfo)
    (updateAddAL _ lc1 (PI_id pinfo) 
      ($ blk2GV TD mb # typ_pointer (PI_typ pinfo) $)) 
      (mb::als1) als2.
Proof.
  intros.
  simpl.
  unfold is_alloca_in_EC.
  destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
  destruct (id_dec (PI_id pinfo) (PI_id pinfo)); try congruence.
  rewrite lookupAL_updateAddAL_eq.
  rewrite Promotability.simpl_blk2GV.
  destruct (Z_eq_dec mb mb); try congruence.
  split; auto.    
    eapply als_simulation_weaken_palloca; eauto.
      apply MemProps.malloc_result in H21.
      intros. intro EQ. subst.
      assert (maxb < Mem.nextblock M1 < Mem.nextblock M1) as J.
        apply Halsbd. simpl. 
        apply in_or_app; auto.
      contradict J. omega.
Qed.

Lemma reg_simulation_update_palloca: forall (pinfo : PhiInfo) 
  (mi : MoreMem.meminj) TD (lc1 lc2 : Opsem.GVsMap)
  (Hlcsim2 : reg_simulation pinfo mi (PI_f pinfo) lc1 lc2)
  (mb : mblock) (mi' : MoreMem.meminj)
  (Hinc : inject_incr mi mi'),
  reg_simulation pinfo mi' (PI_f pinfo)
    (updateAddAL (GVsT DGVs) lc1 (PI_id pinfo)
       ($ blk2GV TD mb # typ_pointer (PI_typ pinfo) $)) lc2.
Proof.
  intros.
  unfold reg_simulation in *.
  destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
  intros.
  assert (J:=@Hlcsim2 i0). clear Hlcsim2.
  destruct (id_dec (PI_id pinfo) i0); subst; auto.
  intros.
  rewrite <- lookupAL_updateAddAL_neq in H; auto.
  eapply J in H; eauto.
  eapply gv_inject_incr; eauto.
Qed.

Lemma inject_incr__preserves__EC_simulation: forall pinfo mi mi' EC1 EC2,
  EC_simulation pinfo mi EC1 EC2 ->
  inject_incr mi mi' ->
  EC_simulation pinfo mi' EC1 EC2.
Admitted.

Lemma inject_incr__preserves__ECs_simulation: forall pinfo mi mi' ECs1 ECs2,
  ECs_simulation pinfo mi ECs1 ECs2 ->
  inject_incr mi mi' ->
  ECs_simulation pinfo mi' ECs1 ECs2.
Proof.
  induction ECs1; destruct ECs2; simpl; intros; auto.
    destruct H as [H1 H2].
    split; eauto using inject_incr__preserves__EC_simulation.
Qed.

Lemma inject_incr__preserves__ftable_simulation: forall mi mi' fs1 fs2,
  ftable_simulation mi fs1 fs2 ->
  inject_incr mi mi' ->
  ftable_simulation mi' fs1 fs2.
Admitted.

Ltac destruct_ctx_return :=
match goal with
| Hwfpp : OpsemPP.wf_State
            {|
            OpsemAux.CurSystem := _;
            OpsemAux.CurTargetData := ?TD;
            OpsemAux.CurProducts := _;
            OpsemAux.Globals := _;
            OpsemAux.FunTable := _
             |} _,
  Hnoalias : Promotability.wf_State _ _ _ _,
  Hsim : State_simulation _ _ _ _ _ ?Cfg2 ?St2 ,
  Hop2 : Opsem.sInsn _ _ _ _ |- _ =>
  destruct TD as [los nts];
  destruct Hwfpp as 
    [Hwfg [HwfSystem [HmInS [_ [
     [Hreach1 [HBinF1 [HFinPs1 _]]] 
     [ 
       [
         [Hreach2 [HBinF2 [HFinPs2 _]]]
         _
       ]
       HwfCall'
     ]]
    ]]]]; subst;
  destruct Cfg2 as [S2 TD2 Ps2 gl2 fs2];
  destruct St2 as [ECs2 M2];
  simpl in Hsim;
  destruct Hsim as [EQ1 [Hpsim [Hstksim [EQ2 [EQ3 Hmsim]]]]]; subst;
  destruct ECs2 as [|[F2 B2 cs2 tmn2 lc2 als2] ECs2]; tinv Hstksim;
  destruct Hstksim as [Hecsim Hstksim];
  destruct ECs2 as [|[F3 B3 cs3 tmn3 lc3 als3] ECs2]; tinv Hstksim;
  destruct Hstksim as [Hecsim' Hstksim];
  unfold EC_simulation in Hecsim;
  destruct Hecsim as 
      [Hfsim2 [Heq1 [Halsim2 [Hbsim2 
        [Heq3 [Heq4 [Hlcsim2 Hcssim2]]]]]]]; subst;
  destruct Hecsim' as 
      [Hfsim2' [Heq1' [Halsim2' [Hbsim2' 
        [Heq3' [Heq4' [Hlcsim2' Hcssim2']]]]]]]; subst;
  destruct Hnoalias as 
    [
      [[Hinscope1' _] [[[Hinscope2' _] [HwfECs' _]] _]] 
      [[Hdisjals _] HwfM]
    ]; simpl in Hdisjals;
  fold Promotability.wf_ECStack in HwfECs';
  apply cmds_simulation_nil_inv in Hcssim2; subst;
  wfCall_inv
end.


Lemma free_allocas_return_sim : forall TD mgb als M1 als2 M2 M1' F l3 ps3 cs0 rid
  RetTy Result lc F' B' i0 n c t v p cs' tmn3 lc' als' EC lc'' gl2 pinfo
  (Hupdate: Opsem.returnUpdateLocals TD (insn_call i0 n c t v p) Result lc lc' 
              gl2 = ret lc'') mi
  (Hfree1: free_allocas TD M1 als = Some M1')
  (Hmsim: Mem_simulation pinfo mgb mi
    ({| Opsem.CurFunction := F;
        Opsem.CurBB := block_intro l3 ps3 (cs0 ++ nil)
                              (insn_return rid RetTy Result);
        Opsem.CurCmds := nil;
        Opsem.Terminator := insn_return rid RetTy Result;
        Opsem.Locals := lc;
        Opsem.Allocas := als |}
             :: {|
                Opsem.CurFunction := F';
                Opsem.CurBB := B';
                Opsem.CurCmds := insn_call i0 n c t v p :: cs';
                Opsem.Terminator := tmn3;
                Opsem.Locals := lc';
                Opsem.Allocas := als' |} :: EC) M1 M2) M2'
  (Halsim: als_simulation pinfo mi F lc als als2)
  (Hfree2: free_allocas TD M2 als2 = Some M2'),
  Mem_simulation pinfo mgb mi 
    ({| Opsem.CurFunction := F';
        Opsem.CurBB := B';
        Opsem.CurCmds := cs';
        Opsem.Terminator := tmn3;
        Opsem.Locals := lc'';
        Opsem.Allocas := als' |} :: EC) M1' M2'.
Admitted.

Lemma returnUpdateLocals_als_simulation: forall pinfo mi F' lc' als' als3 TD i0 n
  c t v p Result lc gl2 lc'' (Hsim: als_simulation pinfo mi F' lc' als' als3)
  (Hupdate: Opsem.returnUpdateLocals TD (insn_call i0 n c t v p) Result lc lc' 
              gl2 = ret lc''),
  als_simulation pinfo mi F' lc'' als' als3.
Admitted.
  
Lemma returnUpdateLocals_reg_simulation: forall pinfo mi F' lc' TD i0 n
  c t v p Result lc gl2 lc'' lc3 lc''0 lc2 F
  (Hsim: reg_simulation pinfo mi F' lc' lc3)
  (Hsim': reg_simulation pinfo mi F lc lc2)
  (Hupdate: Opsem.returnUpdateLocals TD (insn_call i0 n c t v p) Result lc lc' 
              gl2 = ret lc'')
  (Hupdate': Opsem.returnUpdateLocals TD (insn_call i0 n c t v p) Result lc2 lc3
              gl2 = ret lc''0),
  reg_simulation pinfo mi F' lc'' lc''0.
Admitted.

Lemma free_allocas_return_void_sim : forall TD mgb als M1 als2 M2 M1' F l3 ps3 
  cs0 rid lc F' B' i0 n c t v p cs' tmn3 lc' als' EC pinfo mi
  (Hfree1: free_allocas TD M1 als = Some M1')
  (Hmsim: Mem_simulation pinfo mgb mi
    ({| Opsem.CurFunction := F;
        Opsem.CurBB := block_intro l3 ps3 (cs0 ++ nil) (insn_return_void rid);
        Opsem.CurCmds := nil;
        Opsem.Terminator := insn_return_void rid;
        Opsem.Locals := lc;
        Opsem.Allocas := als |}
             :: {|
                Opsem.CurFunction := F';
                Opsem.CurBB := B';
                Opsem.CurCmds := insn_call i0 n c t v p :: cs';
                Opsem.Terminator := tmn3;
                Opsem.Locals := lc';
                Opsem.Allocas := als' |} :: EC) M1 M2) M2'
  (Halsim: als_simulation pinfo mi F lc als als2)
  (Hfree2: free_allocas TD M2 als2 = Some M2'),
  Mem_simulation pinfo mgb mi 
    ({| Opsem.CurFunction := F';
        Opsem.CurBB := B';
        Opsem.CurCmds := cs';
        Opsem.Terminator := tmn3;
        Opsem.Locals := lc';
        Opsem.Allocas := als' |} :: EC) M1' M2'.
Admitted.

Lemma dae_is_sim : forall maxb pinfo mi Cfg1 St1 Cfg2 St2
  (Hwfpi: WF_PhiInfo pinfo) 
  (Hwfgl: sb_ds_gv_inject.wf_globals maxb (OpsemAux.Globals Cfg1)) 
  (Hinbd: 0 <= maxb) (Hnuse: used_in_fdef (PI_id pinfo) (PI_f pinfo) = false)
  (Hwfpp: OpsemPP.wf_State Cfg1 St1) 
  (Hnoalias: Promotability.wf_State maxb pinfo Cfg1 St1) 
  (Hsim: State_simulation pinfo maxb mi Cfg1 St1 Cfg2 St2),
  (forall (Hrem: removable_State pinfo St1) St1' tr1 
     (Hop1: Opsem.sInsn Cfg1 St1 St1' tr1), 
     exists mi',
       State_simulation pinfo maxb mi' Cfg1 St1' Cfg2 St2 /\ tr1 = trace_nil /\
       Values.inject_incr mi mi') /\
  (forall (Hnrem: ~removable_State pinfo St1) St1' St2' tr1 tr2
     (Hop2: Opsem.sInsn Cfg2 St2 St2' tr2) 
     (Hop1: Opsem.sInsn Cfg1 St1 St1' tr1), 
     exists mi',
       State_simulation pinfo maxb mi' Cfg1 St1' Cfg2 St2' /\ tr1 = tr2 /\
       Values.inject_incr mi mi').
Proof.

Local Opaque inscope_of_tmn inscope_of_cmd.

  intros.
  split; intros.
Case "removable state".
  
  destruct Cfg1 as [S1 [los nts] Ps1 gl1 fs1].
  destruct St1 as [ECs1 M1].
  destruct ECs1 as [|[F1 B1 [|c1 cs1] tmn1 lc1 als1] ECs1]; tinv Hrem.
  simpl in Hrem.
  destruct (fdef_dec (PI_f pinfo) F1); subst; tinv Hrem.
  destruct (id_dec (PI_id pinfo) (getCmdLoc c1)); subst; tinv Hrem.
  assert (exists v, 
    c1 = insn_alloca (PI_id pinfo) (PI_typ pinfo) v (PI_align pinfo)) as EQ.
    admit. (* uniqness *)
  destruct EQ as [v EQ]; subst.
  
  destruct Hwfpp as 
    [Hwfg [HwfSystem [HmInS [_ [
     [Hreach1 [HBinF1 [HFinPs1 _]]] 
     [HwfECs Hwfcall]]
    ]]]]; subst.
  fold (@OpsemPP.wf_ECStack DGVs) in HwfECs.

  destruct Hnoalias as 
    [
      [[Hinscope' _] [HwfECs' HwfHT]] 
      [[Hdisjals Halsbd] HwfM]
    ]; simpl in Hdisjals.
  fold Promotability.wf_ECStack in HwfECs'.

  inv Hop1.

  destruct Cfg2 as [S2 TD2 Ps2 gl2 fs2].
  destruct St2 as [ECs2 M2].

  simpl in Hsim.
  destruct Hsim as [EQ1 [Hpsim [Hstksim [EQ2 [EQ3 Hmsim]]]]]; subst.
  destruct ECs2 as [|[F2 B2 cs2 tmn2 lc2 als2] ECs2]; tinv Hstksim.
  destruct Hstksim as [Hecsim Hstksim].
  unfold EC_simulation in Hecsim.
  destruct Hecsim as 
      [Hfsim2 [Heq1 [Halsim2 [Hbsim2 
        [Heq3 [Heq4 [Hlcsim2 Hcssim2]]]]]]]; subst.

  uniq_result.
  eapply mem_simulation__palloca in Hmsim; eauto.
  destruct Hmsim as [mi' [Hmsim [Hinc [Hmi1 Hmi2]]]].
  exists mi'.  
  repeat_solve.
    eapply als_simulation_update_palloca; eauto.
      admit. (*dom*)
        eapply reg_simulation_update_palloca; eauto.
    eapply cmds_simulation_elim_cons_inv; eauto.
    eapply inject_incr__preserves__ECs_simulation; eauto.
    eapply inject_incr__preserves__ftable_simulation; eauto.

Case "unremovable state".
  (sInsn_cases (destruct Hop1) SCase).

SCase "sReturn".
Focus.

  destruct_ctx_return.
  assert (PI_f pinfo <> F' \/ PI_id pinfo <> getCmdLoc (insn_call i0 n c t v p))
    as Hneq.
    admit. (* wf-formedness *)
  apply cmds_simulation_nelim_cons_inv in Hcssim2'; auto.
  destruct Hcssim2' as [cs3' [Heq Hcssim2']]; subst;
  inv Hop2;
  uniq_result.
  eapply free_allocas_return_sim in Hmsim; eauto.
  exists mi.
  repeat_solve.
    eapply returnUpdateLocals_als_simulation; eauto.

    clear - H27 H1 Hlcsim2 Hlcsim2'.
    eapply returnUpdateLocals_reg_simulation with (lc:=lc); eauto.

Unfocus.
      
SCase "sReturnVoid".
Focus.
  destruct_ctx_return.
  assert (PI_f pinfo <> F' \/ PI_id pinfo <> getCmdLoc (insn_call i0 n c t v p))
    as Hneq.
    admit. (* wf-formedness *)
  apply cmds_simulation_nelim_cons_inv in Hcssim2'; auto.
  destruct Hcssim2' as [cs3' [Heq Hcssim2']]; subst;
  inv Hop2;
  uniq_result.
  eapply free_allocas_return_void_sim in Hmsim; eauto.
  exists mi.
  repeat_solve.

Unfocus.

SCase "sBranch".
Focus.

Ltac destruct_ctx_other :=
match goal with
| Hwfpp : OpsemPP.wf_State
            {|
            OpsemAux.CurSystem := _;
            OpsemAux.CurTargetData := ?TD;
            OpsemAux.CurProducts := _;
            OpsemAux.Globals := _;
            OpsemAux.FunTable := _
             |} _,
  Hnoalias : Promotability.wf_State _ _ _ _,
  Hsim : State_simulation _ _ _ _ _ ?Cfg2 ?St2 ,
  Hop2 : Opsem.sInsn _ _ _ _ |- _ =>
  destruct TD as [los nts];
  destruct Hwfpp as 
    [Hwfg [HwfSystem [HmInS [_ [
     [Hreach1 [HBinF1 [HFinPs1 _]]] 
     [ _ HwfCall'
     ]]
    ]]]]; subst;
  destruct Cfg2 as [S2 TD2 Ps2 gl2 fs2];
  destruct St2 as [ECs2 M2];
  simpl in Hsim;
  destruct Hsim as [EQ1 [Hpsim [Hstksim [EQ2 [EQ3 Hmsim]]]]]; subst;
  destruct ECs2 as [|[F2 B2 cs2 tmn2 lc2 als2] ECs2]; tinv Hstksim;
  destruct Hstksim as [Hecsim Hstksim];
  unfold EC_simulation in Hecsim;
  destruct Hecsim as 
      [Hfsim2 [Heq1 [Halsim2 [Hbsim2 
        [Heq3 [Heq4 [Hlcsim2 Hcssim2]]]]]]]; subst;
  destruct Hnoalias as 
    [
      [[Hinscope' _] [HwfECs' HwfHT]] 
      [[Hdisjals _] HwfM]
    ]; simpl in Hdisjals;
  fold Promotability.wf_ECStack in HwfECs'
end.

  destruct_ctx_other.
  apply cmds_simulation_nil_inv in Hcssim2; subst.
  inv Hop2.
  uniq_result.

  assert (block_simulation pinfo F (block_intro l' ps' cs' tmn')
           (block_intro l'0 ps'0 cs'0 tmn'0)) as Hbsim.

Lemma simulation__getOperandValue : forall pinfo maxb mi rm rm2 lc lc2 TD Mem 
    Mem2 gl F v gv gv',
  wf_globals maxb gl -> 
  wf_sb_mi maxb mi Mem Mem2 ->
  reg_simulation pinfo mi TD gl F rm rm2 lc lc2 ->
  getOperandValue TD v lc gl = ret gv ->
  getOperandValue TD v lc2 gl = ret gv' ->
  gv_inject mi gv gv'.




    clear - H22 H1 Hfsim2.
    destruct (isGVZero (los, nts) c); eauto using fdef_sim__block_sim.         
  assert (Hbsim':=Hbsim).
  apply block_simulation_inv in Hbsim'.
  destruct Hbsim' as [Heq1 [Heq2 [Hcssim' Heq5]]]; subst.

  assert (lc' = lc'0) as Heq.
    clear - H2 H23 Hbsim2.
    eapply switchToNewBasicBlock_sim in Hbsim2; eauto.
  subst.

  repeat_solve.
    exists l'0. exists ps'0. exists nil. auto.
    exists l'0. exists ps'0. exists nil. auto.
  
    clear - H2 Hmsim.
    eapply mem_simulation_update_locals in Hmsim; simpl; eauto.
      simpl. intros.
      admit. (* phis <> palloca *)

Unfocus.

SCase "sBranch_uncond".
Focus.
  destruct_ctx_other.
  apply cmds_simulation_nil_inv in Hcssim2; subst.
  inv Hop2.
  uniq_result.

  assert (block_simulation pinfo F (block_intro l' ps' cs' tmn')
           (block_intro l'0 ps'0 cs'0 tmn'0)) as Hbsim.
    eauto using fdef_sim__block_sim.         
  assert (Hbsim':=Hbsim).
  apply block_simulation_inv in Hbsim'.
  destruct Hbsim' as [Heq1 [Heq2 [Hcssim' Heq5]]]; subst.

  assert (lc' = lc'0) as Heq.
    clear - H0 H17 Hbsim2.
    eapply switchToNewBasicBlock_sim in Hbsim2; eauto.
  subst.

  repeat_solve.
    exists l'0. exists ps'0. exists nil. auto.
    exists l'0. exists ps'0. exists nil. auto.
  
    clear - H0 Hmsim.
    eapply mem_simulation_update_locals in Hmsim; simpl; eauto.
      simpl. intros.
      admit. (* phis <> palloca *)
Unfocus.

SCase "sBop". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sFBop". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sExtractValue". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sInsertValue". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sMalloc". 
 
  destruct_ctx_other.
 
  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl; auto;
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.

  assert (mb0 = mb) as EQ.
    destruct Hmsim as [Hmsim _].
    apply MemProps.malloc_result in H25.
    apply MemProps.malloc_result in H2. subst. auto.
  subst.
  repeat_solve.

    destruct Hmsim as [Hmsim1 Hmsim2].
    split; auto.
      apply MemProps.nextblock_malloc in H2.
      apply MemProps.nextblock_malloc in H25.
      rewrite <- H2. rewrite <- H25. rewrite Hmsim1. auto.

      intros.
      eapply Hmsim2 with (ptr:=ptr)(ty:=ty)(al:=al); eauto.
      eapply no_alias_head_tail_update in Hnalias; eauto; simpl; auto.
        intros. admit. (* id <> palloca *)

        (* two cases, if ptr is mb or not, 
           malloc_preserves_mload_inv needs to be extended. *)
        admit. admit.

SCase "sFree". 

  destruct_ctx_other.
 
  apply cmds_simulation_nelim_cons_inv in Hcssim2; auto.
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.

  repeat_solve.
    destruct Hmsim as [Hmsim1 Hmsim2].
    split; auto.
      apply MemProps.nextblock_free in H1.
      apply MemProps.nextblock_free in H22.
      rewrite <- H1. rewrite <- H22. rewrite Hmsim1. auto.

      intros.
      eapply Hmsim2 with (ptr:=ptr)(ty:=ty)(al:=al); 
        eauto using MemProps.free_preserves_mload_inv.
      eapply no_alias_head_tail_irrel in Hnalias; eauto; simpl; auto.

SCase "sAlloca". 

  destruct_ctx_other.
 
  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl; auto;
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.

  assert (mb0 = mb) as EQ.
    destruct Hmsim as [Hmsim _].
    apply MemProps.malloc_result in H25.
    apply MemProps.malloc_result in H2. subst. auto.
  subst.
  repeat_solve.

    destruct Hmsim as [Hmsim1 Hmsim2].
    split; auto.
      apply MemProps.nextblock_malloc in H2.
      apply MemProps.nextblock_malloc in H25.
      rewrite <- H2. rewrite <- H25. rewrite Hmsim1. auto.

      intros.
      eapply Hmsim2 with (ptr:=ptr)(ty:=ty)(al:=al); eauto.
      eapply no_alias_head_tail_update in Hnalias; eauto; simpl; auto.
        intros.
        admit. (* if id = palloca, then lc2 cannot contain pid *)

        (* two cases, if ptr is mb or not, 
           malloc_preserves_mload_inv needs to be extended. *)
        admit. admit. 

SCase "sLoad". 
  destruct_ctx_other.

  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl; auto;
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.

  assert (gv = gv0) as EQ.
    admit. (* no load from pid *)
  subst.
  repeat_solve.

    eapply mem_simulation_update_locals in Hmsim; simpl; eauto.
      simpl. intros.
      admit. (* lid <> pid *)

SCase "sStore". 

  destruct_ctx_other.
 
  assert (PI_f pinfo = F -> 
          store_in_cmd (PI_id pinfo) (insn_store sid t v1 v2 align0) = false)
         as J.
    clear - Hnrem. simpl in Hnrem.
    destruct v2; auto.
    intros. subst.
    destruct (fdef_dec (PI_f pinfo) (PI_f pinfo)); try congruence.
    simpl.
    destruct (id_dec i0 (PI_id pinfo)); subst; auto.
    destruct (id_dec (PI_id pinfo) (PI_id pinfo)); try congruence.
    contradict Hnrem; auto.
  apply cmds_simulation_nelim_cons_inv in Hcssim2; auto.
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.

  repeat_solve.
    destruct Hmsim as [Hmsim1 Hmsim2].
    split; auto.
      apply MemProps.nextblock_mstore in H3.
      apply MemProps.nextblock_mstore in H28.
      rewrite <- H3. rewrite <- H28. rewrite Hmsim1. auto.

      intros.
      eapply Hmsim2 with (ptr:=ptr)(ty:=ty)(al:=al); eauto.
      eapply no_alias_head_tail_irrel in Hnalias; eauto; simpl; auto.
        (* two cases, if ptr overlaps with stored ptr or not *)
        admit. admit.

SCase "sGEP". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sTrunc". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sExt". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sCast". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sIcmp". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sFcmp". abstract (destruct_ctx_other; dse_is_sim_common_case).
SCase "sSelect". 
  destruct_ctx_other.

  apply cmds_simulation_nelim_cons_inv in Hcssim2; simpl; auto;
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst;
  inv Hop2; uniq_result.

  repeat_solve.
    destruct (isGVZero (los,nts) c).
      eapply mem_simulation_update_locals in Hmsim; simpl; eauto.
        simpl. intros.
        admit. (* lid <> pid *)
      eapply mem_simulation_update_locals in Hmsim; simpl; eauto.
        simpl. intros.
        admit. (* lid <> pid *)

SCase "sCall".

  destruct_ctx_other.
  assert (Hcssim2':=Hcssim2).
  apply cmds_simulation_nelim_cons_inv in Hcssim2; auto.
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst.

  inv Hop2.

  SSCase "SCall".

  uniq_result.
  assert (Hfsim1:=Hpsim).
  eapply lookupFdefViaPtr__simulation in Hfsim1; eauto.

  assert (Hbsim1:=Hfsim1).
  eapply fdef_simulation__entry_block_simulation in Hbsim1; eauto.
  assert (Hbsim1':=Hbsim1).
  apply block_simulation_inv in Hbsim1'.
  destruct Hbsim1' as [Heq' [Hpsim1' [Hcsim1' Htsim1']]]; subst.
  repeat_solve.
    exists l'0. exists ps'0. exists nil. auto.
    exists l'0. exists ps'0. exists nil. auto.

    apply fdef_simulation_inv in Hfsim1.
    destruct Hfsim1 as [Heq _]. inv Heq. uniq_result.
    auto.

    destruct Hmsim as [Hmsim1 Hmsim2].
    split; auto.
      intros.
      eapply Hmsim2 with (ptr:=ptr)(ty:=ty)(al:=al); eauto.
      clear Hmsim2.
      apply no_alias_head_tail_cons_and in Hnalias.
      destruct Hnalias as [Hnalias1 Hnalias2]; auto.

  SSCase "sExCall".

  uniq_result.

  clear - H28 H1 Hpsim.
  eapply lookupFdefViaPtr__simulation_l2r in H1; eauto.
  destruct H1 as [f2 [H1 H2]].
  apply OpsemAux.lookupExFdecViaPtr_inversion in H28.
  apply OpsemAux.lookupFdefViaPtr_inversion in H1.
  destruct H28 as [fn [J1 [J2 J3]]].
  destruct H1 as [fn' [J4 J5]].
  uniq_result.   

SCase "sExCall". 

  destruct_ctx_other.
  assert (Hcssim2':=Hcssim2).
  apply cmds_simulation_nelim_cons_inv in Hcssim2; auto.
  destruct Hcssim2 as [cs3' [Heq Hcssim2]]; subst.

  inv Hop2.

  SSCase "SCall".

  uniq_result.

  clear - H29 H1 Hpsim.
  eapply lookupExFdecViaPtr__simulation_l2r in H1; eauto.
  apply OpsemAux.lookupExFdecViaPtr_inversion in H1.
  apply OpsemAux.lookupFdefViaPtr_inversion in H29.
  destruct H1 as [fn [J1 [J2 J3]]].
  destruct H29 as [fn' [J4 J5]].
  uniq_result.   

  SSCase "sExCall".

  uniq_result.

  assert (Hlkdec:=Hpsim).
  eapply lookupExFdecViaPtr__simulation_l2r in Hlkdec; eauto.
  uniq_result.
  eapply callExternalFunction__Mem_simulation in Hmsim; eauto.
  destruct Hmsim as [EQ Hmsim]; subst.
  uniq_result.
  repeat_solve.
    eapply mem_simulation_update_locals in Hmsim; simpl; eauto.
      simpl. intros. admit. (* cid <> pid *)
    
Transparent inscope_of_tmn inscope_of_cmd.

Qed.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
