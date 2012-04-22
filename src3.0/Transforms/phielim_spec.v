Require Import vellvm.
Require Import primitives.
Require Import mem2reg.

Lemma eliminate_phi_false_spec: forall f p f'
  (Helim: (f', false) = eliminate_phi f p), f = f'.
Admitted. (* spec *)

Lemma eliminate_phis_false_spec: forall f' f ps0
  (Helim: (f', false) = eliminate_phis f ps0 ), f' = f.
Proof.
  induction ps0 as [|p]; simpl; intros.
    congruence.

    remember (eliminate_phi f p) as R.
    destruct R as []; inv Helim.
    destruct_if; auto.
    apply eliminate_phi_false_spec in HeqR. subst. auto.
Qed.

(* vid = phi [vid vid ... vid] *)
Inductive identity_phi: phinode -> Prop :=
| identity_phi_intro: forall vid ty vls
    (Hid: forall v0 l0, In (v0, l0) vls -> v0 = value_id vid),
    identity_phi (insn_phi vid ty vls)
.

Lemma identity_phi_cannot_be_in_reachable_blocks: forall S M p f
  l0 ps0 cs0 tmn0 (Hreach: reachable f l0) 
  (Hwf: wf_fdef S M f) (Huniq: uniqFdef f)
  (HBinF: blockInFdefB (block_intro l0 ps0 cs0 tmn0) f = true)
  (Hin: In p ps0) (Hid: identity_phi p),
  False. 
Admitted. (* dom *)

(* vid = phi [vid v ... vid v] *)
Inductive assigned_phi (v:value): phinode -> Prop :=
| assigned_phi_intro: forall vid ty vls
    (Hex: exists l0, In (v, l0) vls)
    (Hassign: forall v0 l0, In (v0, l0) vls -> v0 = value_id vid \/ v0 = v),
    assigned_phi v (insn_phi vid ty vls)
.

Lemma assigned_phi__domination: forall S M p f l0 ps0 cs0 tmn0
  (Hwf: wf_fdef S M f) (Huniq: uniqFdef f)
  (HBinF: blockInFdefB (block_intro l0 ps0 cs0 tmn0) f = true) 
  (Hin: In p ps0) v (Has: assigned_phi v p),
  valueDominates f v (value_id (getPhiNodeID p)).
Admitted. (* dom *)

Lemma eliminate_phi_true_spec: forall S M f b f'
  (Hreach: isReachableFromEntry f b) p 
  (Hwf: wf_fdef S M f) (Huniq: uniqFdef f)
  (HBinF: phinodeInFdefBlockB p f b = true)
  (Helim: (f', true) = eliminate_phi f p),
  exists v, assigned_phi v p /\ 
    f' = remove_fdef (getPhiNodeID p) (subst_fdef (getPhiNodeID p) v f).
Admitted. (* spec *)

Lemma eliminate_phis_true_spec': forall f b f' S M 
  (Hwf: wf_fdef S M f) (Huniq: uniqFdef f)
  (Hreach: isReachableFromEntry f b) ps
  (HBinF: forall p, In p ps -> phinodeInFdefBlockB p f b = true)
  (Helim: (f', true) = eliminate_phis f ps),
  exists p, In p ps /\ exists v, assigned_phi v p /\ 
    f' = remove_fdef (getPhiNodeID p) (subst_fdef (getPhiNodeID p) v f).
Proof.
  induction ps as [|p]; simpl; intros.
    inv Helim.

    remember (eliminate_phi f p) as R.
    destruct R as []; inv Helim.
    destruct_if.
      exists p.
      split; auto. 
      eapply eliminate_phi_true_spec in HeqR; eauto.

      apply eliminate_phi_false_spec in HeqR. subst. 
      apply IHps in H1; auto. 
      destruct H1 as [p' [Hin [v [H1 H2]]]].
      eauto 6.
Qed.
    
Lemma eliminate_phis_true_spec: forall f f' l0 S M 
  (Hwf: wf_fdef S M f) (Huniq: uniqFdef f)
  (Hreach: reachable f l0) ps cs0 tmn0
  (HBinF: blockInFdefB (block_intro l0 ps cs0 tmn0) f = true)
  (Helim: (f', true) = eliminate_phis f ps),
  exists p, In p ps /\ exists v, assigned_phi v p /\ 
    f' = remove_fdef (getPhiNodeID p) (subst_fdef (getPhiNodeID p) v f).
Proof.
  intros.
  eapply eliminate_phis_true_spec' with (b:=block_intro l0 ps cs0 tmn0); 
    simpl; eauto 1.
  intros.
  bsplit; auto. simpl. solve_in_list.
Qed.

Lemma assigned_phi__wf_value: forall S M p f l0 ps0 cs0 tmn0
  (Hwf: wf_fdef S M f) (Huniq: uniqFdef f)
  (HBinF: blockInFdefB (block_intro l0 ps0 cs0 tmn0) f = true) 
  (Hin: In p ps0) v (Hassign: assigned_phi v p),
  forall ty, 
    lookupTypViaIDFromFdef f (getPhiNodeID p) = Some ty ->
    wf_value S M f v ty.
Admitted. (* spec *)
