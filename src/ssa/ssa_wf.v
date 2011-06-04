Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "./compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Add LoadPath "../".
Require Import ssa_def.
Require Import ssa_lib.
Require Import ssa_static.
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
Require Import GraphBasics.Digraphs.

Export LLVMwf.

Fixpoint blocks_to_Vset (bs:blocks) : V_set :=
match bs with
| nil => V_empty
| block_intro l _ _ _ :: bs' => V_union (V_single (index l)) (blocks_to_Vset bs')
end.

Fixpoint blocks_to_Aset (bs:blocks) : A_set :=
match bs with
| nil => A_empty
| block_intro l0 _ _ (insn_br _ _ l1 l2) :: bs' => 
    A_union (A_single (A_ends (index l0) (index l1)))
      (A_union (A_single (A_ends (index l0) (index l2))) (blocks_to_Aset bs'))
| block_intro l0 _ _ (insn_br_uncond _ l1) :: bs' => 
    A_union (A_single (A_ends (index l0) (index l1))) (blocks_to_Aset bs')
| block_intro l0 _ _ _ :: bs' => blocks_to_Aset bs'
end.

Lemma blocks_to_Vset_spec : forall (blocks5 : blocks) (l0 : l) 
  (H4 : l0 `notin` dom (genLabel2Block_blocks blocks5)),
  ~ blocks_to_Vset blocks5 (index l0).
Proof.
  intros.
  induction blocks5; intro J.
    inversion J.

    destruct a. simpl in *.
    inversion J; subst.
      inversion H; subst.
      fsetdec.

      apply IHblocks5; try solve [auto | fsetdec].
Qed.

Lemma blocks_to_CFG_no_edges : forall InF S MI FI bs,
  wf_blocks InF S MI FI bs ->
  uniq (genLabel2Block_blocks bs) ->
  exists cfg : Digraph (blocks_to_Vset bs) A_empty, True.
Proof.
  intros InF S MI FI bs Hwfbs Huniq. 
  induction Hwfbs; simpl; intros.
    exists D_empty. auto.
    
    destruct block5 as [l0 ? ? tmn].
    inversion Huniq; subst.
    apply IHHwfbs in H2.
    destruct H2 as [cfg _].
    assert (~ blocks_to_Vset blocks5 (index l0)) as J.
      eapply blocks_to_Vset_spec; eauto.
    destruct tmn;
      apply D_vertex with (x:=index l0) in cfg; 
        try solve [auto | exists cfg; auto].
Qed.

Lemma Included_union_right : forall U (E F C: U_set U), 
  Included U (Union U E F) C ->
  Included U F C.
Proof.
        unfold Included in |- *; intros.
        apply H. apply In_right. trivial.
Qed.

Lemma Included_union_left : forall U (E F C: U_set U), 
  Included U (Union U E F) C ->
  Included U E C.
Proof.
        unfold Included in |- *; intros.
        apply H. apply In_left. trivial.
Qed.

Lemma blocks_to_CFG : forall InF S MI FI bs Vs,
  wf_blocks InF S MI FI bs ->
  uniq (genLabel2Block_blocks bs) ->
  V_included (blocks_to_Vset bs) Vs ->
  Digraph Vs A_empty ->
  exists cfg : Digraph Vs (blocks_to_Aset bs), True.
Proof.
  intros InF S MI FI bs Vs Hwfbs Huniq Hinc Hcfg. 
  induction Hwfbs; simpl in *; intros.
    exists Hcfg. auto.
    
    destruct block5 as [l0 ? ? tmn]; simpl in *.
    inversion Huniq; subst.
    assert (J:=Hinc).
    apply Included_union_left in J.
    apply Included_union_right in Hinc.
    apply IHHwfbs in H2; auto.
    destruct H2 as [cfg _].
    destruct tmn.
      exists cfg. auto.
      exists cfg. auto.

      apply D_arc with (x:=index l0)(y:=index l2) in cfg.
        apply D_arc with (x:=index l0)(y:=index l1) in cfg.
          exists cfg. auto.
          unfold Included in J. apply J. unfold V_single. apply In_single.
Admitted.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV" "-I" "~/SVN/sol/vol/src/GraphBasics" "-impredicative-set") ***
*** End: ***
 *)
