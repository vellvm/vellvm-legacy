Require Import Metatheory.
Require Import syntax.
Require Import infrastructure.
Require Import dom_tree.
Require Import dom_list.
Require Import typings_props.
Require Import typings.
Import LLVMsyntax.
Import LLVMinfra.
Import LLVMtypings.

(* Well-formed programs give well-formed dominator trees. *)
Section wf_fdef__create_dom_tree_correct.

Variable (S:system) (M:module) (f:fdef) (dt:@DTree l) (le:l).
Hypothesis (Hwfdef: wf_fdef S M f) (Huniq: uniqFdef f)
           (Hcreate: AlgDom.create_dom_tree f = Some dt)
           (Hentry: getEntryLabel f = Some le).

Lemma wf_fdef__dtree_edge_iff_idom: forall p0 ch0,
    is_dtree_edge eq_atom_dec dt p0 ch0 = true <-> 
      (imm_domination f p0 ch0 /\ reachable f ch0).
Proof.
  intros.
  eapply AlgDom.dtree_edge_iff_idom; unfold AlgDom.branchs_in_fdef;
    intros; eauto using entry_no_preds, branches_in_bound_fdef.
Qed.

Lemma wf_fdef__create_dom_tree__wf_dtree: 
  ADProps.wf_dtree (successors f) le eq_atom_dec dt.
Proof.
  intros.
  eapply AlgDom.create_dom_tree__wf_dtree; unfold AlgDom.branchs_in_fdef;
    intros; eauto using entry_no_preds, branches_in_bound_fdef.
Qed.

End wf_fdef__create_dom_tree_correct.
