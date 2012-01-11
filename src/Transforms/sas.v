Add LoadPath "../Vellvm/ott".
Add LoadPath "../Vellvm/monads".
Add LoadPath "../Vellvm/compcert".
Add LoadPath "../Vellvm/GraphBasics".
Add LoadPath "../Vellvm".
Add LoadPath "../../../theory/metatheory_8.3".
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
Require Import id_rhs_val.
Require Import palloca_props.
Require Import memory_props.

Definition load_in_cmd (id':id) (c:cmd) : bool :=
match c with
| insn_load _ _ ptr _ => used_in_value id' ptr
| _ => false
end.

Definition load_in_cmds (id':id) (cs:cmds) : bool := 
(List.fold_left (fun re c => re || load_in_cmd id' c) cs false).

Definition sas (sid1 sid2: id) (v1 v2:value) (cs2:cmds) (b:block) 
  (pinfo:PhiInfo) : Prop :=         
blockInFdefB b (PI_f pinfo) = true /\
load_in_cmds (PI_id pinfo) cs2 = false /\
let '(block_intro _ _ cs _) := b in
exists cs1, exists cs3,
  cs = 
  cs1 ++ 
  insn_store sid1 (PI_typ pinfo) v1 (value_id (PI_id pinfo)) (PI_align pinfo) ::
  cs2 ++ 
  insn_store sid2 (PI_typ pinfo) v2 (value_id (PI_id pinfo)) (PI_align pinfo) ::
  cs3.

Record SASInfo (pinfo: PhiInfo) := mkSASInfo {
  SAS_sid1 : id;
  SAS_sid2 : id;
  SAS_value1 : value;
  SAS_value2 : value;
  SAS_tail : cmds;
  SAS_block : block;
  SAS_prop: sas SAS_sid1 SAS_sid2 SAS_value1 SAS_value2 SAS_tail SAS_block pinfo
}.

Definition fdef_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) f1 f2 
  : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then 
    remove_fdef (SAS_sid1 pinfo sasinfo) f1 = f2
  else f1 = f2.

Definition cmds_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) (f1:fdef) 
  cs1 cs2 : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then 
    remove_cmds (SAS_sid1 pinfo sasinfo) cs1 = cs2
  else cs1 = cs2.

Definition block_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) (f1:fdef) 
  b1 b2 : Prop :=
  if (fdef_dec (PI_f pinfo) f1) then 
    remove_block (SAS_sid1 pinfo sasinfo) b1 = b2
  else b1 = b2.

Definition products_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) Ps1 Ps2
  : Prop :=
List.Forall2 
  (fun P1 P2 =>
   match P1, P2 with
   | product_fdef f1, product_fdef f2 => fdef_simulation pinfo sasinfo f1 f2
   | _, _ => P1 = P2
   end) Ps1 Ps2.

Definition system_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) S1 S2 
  : Prop :=
List.Forall2 
  (fun M1 M2 =>
   match M1, M2 with
   | module_intro los1 nts1 Ps1, module_intro los2 nts2 Ps2 =>
       los1 = los2 /\ nts1 = nts2 /\ 
       products_simulation pinfo sasinfo Ps1 Ps1
   end) S1 S2.

Definition EC_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) 
  (EC1 EC2:@Opsem.ExecutionContext DGVs) : Prop :=
  match (EC1, EC2) with
  | (Opsem.mkEC f1 b1 cs1 tmn1 lc1 als1, 
     Opsem.mkEC f2 b2 cs2 tmn2 lc2 als2) =>
       fdef_simulation pinfo sasinfo f1 f2 /\
       tmn1 = tmn2 /\
       als1 = als2 /\
       block_simulation pinfo sasinfo f1 b1 b2 /\
       (exists l1, exists ps1, exists cs11, 
         b1 = block_intro l1 ps1 (cs11++cs1) tmn1)
         /\
       (exists l2, exists ps2, exists cs21,
         b2 = block_intro l2 ps2 (cs21++cs2) tmn2) /\
       lc1 = lc2 /\
       cmds_simulation pinfo sasinfo f1 cs1 cs2
  end.

Fixpoint ECs_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) 
  (ECs1 ECs2:@Opsem.ECStack DGVs) : Prop :=
match ECs1, ECs2 with
| nil, nil => True
| EC1::ECs1', EC2::ECs2' => 
    EC_simulation pinfo sasinfo EC1 EC2 /\ 
    ECs_simulation pinfo sasinfo ECs1' ECs2'
| _, _ => False
end.

Definition cs_follow_dead_store (pinfo:PhiInfo) (sasinfo: SASInfo pinfo)
  (cs:cmds) : Prop :=
let '(block_intro _ _ cs0 _) := SAS_block pinfo sasinfo in
forall cs1 cs3, 
  cs0 = 
    cs1 ++ 
    insn_store (SAS_sid1 pinfo sasinfo) (PI_typ pinfo) 
      (SAS_value1 pinfo sasinfo) (value_id (PI_id pinfo)) (PI_align pinfo) ::
    SAS_tail pinfo sasinfo ++ 
    cs3 ->
  (exists csa, exists csb, 
    cs = csb ++ cs3 /\ SAS_tail pinfo sasinfo = csa ++ csb).

Definition EC_follow_dead_store (pinfo:PhiInfo) (sasinfo: SASInfo pinfo)
  (ec:@Opsem.ExecutionContext DGVs) : Prop :=
Opsem.CurFunction ec = PI_f pinfo /\
Opsem.CurBB ec = SAS_block pinfo sasinfo /\
cs_follow_dead_store pinfo sasinfo (Opsem.CurCmds ec).

Definition undead_head_in_tail (pinfo:PhiInfo) (sasinfo: SASInfo pinfo) ptr
  (ec0:@Opsem.ExecutionContext DGVs) : Prop :=
forall gvsa (Heq: Opsem.CurFunction ec0 = PI_f pinfo)
  (Hlkup: lookupAL _ (Opsem.Locals ec0) (PI_id pinfo) = Some gvsa),
  MemProps.no_alias ptr gvsa \/
  ~ MemProps.no_alias ptr gvsa /\ EC_follow_dead_store pinfo sasinfo ec0.

Definition undead_head_tail (pinfo:PhiInfo) (sasinfo: SASInfo pinfo) ptr 
  (ecs':list Opsem.ExecutionContext) : Prop :=
  forall ec0 (Hin: In ec0 ecs'), undead_head_in_tail pinfo sasinfo ptr ec0.

Definition Mem_simulation (pinfo:PhiInfo) (sasinfo: SASInfo pinfo) TD 
  (ecs1:list Opsem.ExecutionContext) Mem1 Mem2 : Prop :=
Mem.nextblock Mem1 = Mem.nextblock Mem2 /\
forall ptr ty al gvs1 gvs2 
  (Hnalias: undead_head_tail pinfo sasinfo ptr ecs1)
  (Hld1: mload TD Mem1 ptr ty al = Some gvs1)
  (Hld2: mload TD Mem2 ptr ty al = Some gvs2),
  gvs1 = gvs2.

Definition State_simulation (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) 
  (Cfg1:OpsemAux.Config) (St1:Opsem.State) 
  (Cfg2:OpsemAux.Config) (St2:Opsem.State) : Prop :=
let '(OpsemAux.mkCfg S1 TD1 Ps1 gl1 fs1) := Cfg1 in
let '(OpsemAux.mkCfg S2 TD2 Ps2 gl2 fs2) := Cfg2 in
match (St1, St2) with
| (Opsem.mkState ECs1 M1, Opsem.mkState ECs2 M2) =>
    TD1 = TD2 /\ 
    products_simulation pinfo sasinfo Ps1 Ps2 /\
    ECs_simulation pinfo sasinfo ECs1 ECs2 /\
    gl1 = gl2 /\ fs1 = fs2 /\ Mem_simulation pinfo sasinfo TD1 ECs1 M1 M2
end.

Definition removable_State (pinfo: PhiInfo) (sasinfo: SASInfo pinfo) 
  (St:@Opsem.State DGVs) : Prop :=
match St with
| Opsem.mkState
    (Opsem.mkEC f b 
      (insn_store sid _ _ _ _ :: cs) 
      tmn lc als::_) _ => 
    if (fdef_dec (PI_f pinfo) f) then 
      if (id_dec sid (SAS_sid1 pinfo sasinfo)) 
      then True else False
    else False
| _ => False
end.

Lemma dse_is_sim : forall maxb pinfo (sasinfo: SASInfo pinfo) Cfg1 St1 Cfg2 St2
  (Hwfpi: WF_PhiInfo pinfo) 
  (Hwfpp: OpsemPP.wf_State Cfg1 St1) 
  (Hnoalias: Promotability.wf_State maxb pinfo Cfg1 St1) 
  (Hsim: State_simulation pinfo sasinfo Cfg1 St1 Cfg2 St2),
  (forall (Hrem: removable_State pinfo sasinfo St1) St1' tr1 
     (Hop1: Opsem.sInsn Cfg1 St1 St1' tr1), 
     State_simulation pinfo sasinfo Cfg1 St1' Cfg2 St2 /\ tr1 = trace_nil) /\
  (forall (Hnrem: ~removable_State pinfo sasinfo St1) St1' St2' tr1 tr2
     (Hop2: Opsem.sInsn Cfg2 St2 St2' tr2) 
     (Hop1: Opsem.sInsn Cfg1 St1 St1' tr1), 
     State_simulation pinfo sasinfo Cfg1 St1' Cfg2 St2' /\ tr1 = tr2).
Admitted.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
