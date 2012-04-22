Require Import vellvm.
Require Import Lattice.

Definition DGVMap := @Opsem.GVsMap DGVs.

(* The invariant is fine to prove subst v1 by v2 in f when v2 >> v1.
   when value_in_scope v1 ids0, we must have value_in_scope v2 ids0. 
*)
Definition wf_defs (v1 v2:value) F TD gl (f:fdef) (lc:DGVMap) ids0: Prop :=
F = f ->
forall gvs1 gvs2,
  value_in_scope v1 ids0 ->
  Opsem.getOperandValue TD v1 lc gl = Some gvs1 ->
  Opsem.getOperandValue TD v2 lc gl = Some gvs2 ->
  gvs1 = gvs2.

Definition inscope_of_ec (ec:@Opsem.ExecutionContext DGVs) : option ids :=
let '(Opsem.mkEC f b cs tmn lc als) := ec in
match cs with
| nil => inscope_of_tmn f b tmn
| c::_ => inscope_of_cmd f b c
end.

Definition wf_ExecutionContext v1 v2 F TD gl (ps:list product)
  (ec:Opsem.ExecutionContext) : Prop :=
match inscope_of_ec ec with
| Some ids0 =>
    wf_defs v1 v2 F TD gl (Opsem.CurFunction ec) (Opsem.Locals ec) ids0
| _ => False
end.

Fixpoint wf_ECStack v1 v2 F TD gl (ps:list product) (ecs:Opsem.ECStack) : Prop :=
match ecs with
| nil => True
| ec::ecs' =>
    wf_ExecutionContext v1 v2 F TD gl ps ec /\ wf_ECStack v1 v2 F TD gl ps ecs'
end.

Definition wf_State v1 v2 F (cfg:OpsemAux.Config) (S:Opsem.State) : Prop :=
let '(OpsemAux.mkCfg s td ps gl _ ) := cfg in
let '(Opsem.mkState ecs _) := S in
wf_ECStack v1 v2 F td gl ps ecs.

Lemma wf_defs_eq : forall ids2 ids1 v1 v2 F td gl F' lc',
  AtomSet.set_eq _ ids1 ids2 ->
  wf_defs v1 v2 F td gl F' lc' ids1 ->
  wf_defs v1 v2 F td gl F' lc' ids2.
Proof.
  intros.
  intros EQ gv1 gv2 Hin1 Hget1 Hget2; subst.
  destruct H as [J1 J2].
  eapply H0; eauto.
    destruct v1; simpl in *; eauto.
Qed.

