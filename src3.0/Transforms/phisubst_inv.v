Require Import vellvm.
Require Import primitives.
Require Import subst_inv.
Require Import phielim_spec.

Record PEInfo := mkPEInfo {
  PEI_f : fdef;
  PEI_p : phinode;
  PEI_v : value;
  PEI_lkup: lookupInsnViaIDFromFdef PEI_f (getPhiNodeID PEI_p) = 
              Some (insn_phinode PEI_p);
  PEI_assign: assigned_phi PEI_v PEI_p
}.

Lemma preservation: forall (cfg1 : OpsemAux.Config)
  (S1 S1' : Opsem.State) (tr : trace) (pi: PEInfo)
  (Hcfg: OpsemPP.wf_Config cfg1) (Hpp: OpsemPP.wf_State cfg1 S1)
  (Hop: Opsem.sInsn cfg1 S1 S1' tr)
  (HwfS : subst_inv.wf_State (value_id (getPhiNodeID (PEI_p pi))) (PEI_v pi) 
          (PEI_f pi) cfg1 S1),
  subst_inv.wf_State (value_id (getPhiNodeID (PEI_p pi))) (PEI_v pi) (PEI_f pi) 
    cfg1 S1'.
Admitted.

Lemma s_genInitState__inv: forall (S : system) (main : id) (pi: PEInfo) 
  (VarArgs : list (GVsT DGVs)) (cfg : OpsemAux.Config) (IS : Opsem.State)
  (HwfS: wf_system S)
  (Hinit: Opsem.s_genInitState S main VarArgs Mem.empty = ret (cfg, IS)),
  wf_State (value_id (getPhiNodeID (PEI_p pi))) (PEI_v pi) (PEI_f pi) cfg IS.
Admitted.
