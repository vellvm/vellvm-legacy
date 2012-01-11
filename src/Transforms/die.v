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
Require Import primitives.

Definition pure_cmd (c:cmd) : Prop :=
match c with
| insn_alloca _ _ _ _  
| insn_malloc _ _ _ _  
| insn_store _ _ _ _ _
| insn_call _ _ _ _ _ _ => False
| _ => True
end.

Record DIInfo := mkDIInfo {
  DI_f : fdef;
  DI_id : id;
  DI_pure : forall c, 
               lookupInsnViaIDFromFdef DI_f DI_id = Some (insn_cmd c) -> 
               pure_cmd c;
  DI_unused : used_in_fdef DI_id DI_f = false
}.

Definition fdef_simulation (diinfo: DIInfo) f1 f2 : Prop :=
  if (fdef_dec (DI_f diinfo) f1) then remove_fdef (DI_id diinfo) f1 = f2
  else f1 = f2.

Definition cmds_simulation (diinfo: DIInfo) (f1:fdef) cs1 cs2 : Prop :=         
  if (fdef_dec (DI_f diinfo) f1) then remove_cmds (DI_id diinfo) cs1 = cs2
  else cs1 = cs2.

Definition block_simulation (diinfo: DIInfo) (f1:fdef) b1 b2 : Prop :=
  if (fdef_dec (DI_f diinfo) f1) then remove_block (DI_id diinfo) b1 = b2
  else b1 = b2.

Definition products_simulation (diinfo: DIInfo) Ps1 Ps2 : Prop :=
List.Forall2 
  (fun P1 P2 =>
   match P1, P2 with
   | product_fdef f1, product_fdef f2 => fdef_simulation diinfo f1 f2
   | _, _ => P1 = P2
   end) Ps1 Ps2.

Definition system_simulation (diinfo: DIInfo) S1 S2 : Prop :=
List.Forall2 
  (fun M1 M2 =>
   match M1, M2 with
   | module_intro los1 nts1 Ps1, module_intro los2 nts2 Ps2 =>
       los1 = los2 /\ nts1 = nts2 /\ 
       products_simulation diinfo Ps1 Ps1
   end) S1 S2.

Definition reg_simulation (diinfo: DIInfo) (F1:fdef) 
  (lc1 lc2:@Opsem.GVsMap DGVs) : Prop :=
  if (fdef_dec (DI_f diinfo) F1) then 
    forall i0, i0 <> DI_id diinfo -> lookupAL _ lc1 i0 = lookupAL _ lc2 i0
  else
    lc1 = lc2.

Definition EC_simulation (diinfo: DIInfo) (EC1 EC2:@Opsem.ExecutionContext DGVs) 
  : Prop :=
  match (EC1, EC2) with
  | (Opsem.mkEC f1 b1 cs1 tmn1 lc1 als1, 
     Opsem.mkEC f2 b2 cs2 tmn2 lc2 als2) =>
       fdef_simulation diinfo f1 f2 /\
       tmn1 = tmn2 /\
       als1 = als2 /\
       block_simulation diinfo f1 b1 b2 /\
       (exists l1, exists ps1, exists cs11, 
         b1 = block_intro l1 ps1 (cs11++cs1) tmn1)
         /\
       (exists l2, exists ps2, exists cs21,
         b2 = block_intro l2 ps2 (cs21++cs2) tmn2) /\
       reg_simulation diinfo f1 lc1 lc2 /\
       cmds_simulation diinfo f1 cs1 cs2
  end.

Fixpoint ECs_simulation (diinfo: DIInfo) (ECs1 ECs2:@Opsem.ECStack DGVs) 
  : Prop :=
match ECs1, ECs2 with
| nil, nil => True
| EC1::ECs1', EC2::ECs2' => 
    EC_simulation diinfo EC1 EC2 /\ ECs_simulation diinfo ECs1' ECs2'
| _, _ => False
end.

Definition State_simulation (diinfo: DIInfo)
  (Cfg1:OpsemAux.Config) (St1:Opsem.State) 
  (Cfg2:OpsemAux.Config) (St2:Opsem.State) : Prop :=
let '(OpsemAux.mkCfg S1 TD1 Ps1 gl1 fs1) := Cfg1 in
let '(OpsemAux.mkCfg S2 TD2 Ps2 gl2 fs2) := Cfg2 in
match (St1, St2) with
| (Opsem.mkState ECs1 M1, Opsem.mkState ECs2 M2) =>
    TD1 = TD2 /\ 
    products_simulation diinfo Ps1 Ps2 /\
    ECs_simulation diinfo ECs1 ECs2 /\
    gl1 = gl2 /\ fs1 = fs2 /\ M1 = M2
end.

Definition removable_State (diinfo: DIInfo) (St:@Opsem.State DGVs) : Prop :=
match St with
| Opsem.mkState
    (Opsem.mkEC f b (c :: cs) tmn lc als::_) _ => 
    if (fdef_dec (DI_f diinfo) f) then 
      if (id_dec (DI_id diinfo) (getCmdLoc c)) then True else False
    else False
| _ => False
end.

Lemma removable_State_dec : forall diinfo St,
  removable_State diinfo St \/ ~ removable_State diinfo St.
Proof.
  destruct St. 
  destruct ECS as [|[]]; auto.
  destruct CurCmds; auto.
  simpl.
  destruct (fdef_dec (DI_f diinfo) CurFunction); auto.
  destruct (id_dec (DI_id diinfo) (getCmdLoc c)); auto.
Qed.

Lemma die_is_sim : forall diinfo Cfg1 St1 Cfg2 St2
  (Hwfpp: OpsemPP.wf_State Cfg1 St1) 
  (Hsim: State_simulation diinfo Cfg1 St1 Cfg2 St2),
  (forall (Hrem: removable_State diinfo St1) St1' tr1 
     (Hop1: Opsem.sInsn Cfg1 St1 St1' tr1), 
      State_simulation diinfo Cfg1 St1' Cfg2 St2 /\ tr1 = trace_nil) /\
  (forall (Hnrem: ~removable_State diinfo St1) St1' St2' tr1 tr2
     (Hop2: Opsem.sInsn Cfg2 St2 St2' tr2) 
     (Hop1: Opsem.sInsn Cfg1 St1 St1' tr1), 
     State_simulation diinfo Cfg1 St1' Cfg2 St2' /\ tr1 = tr2).
Admitted.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
