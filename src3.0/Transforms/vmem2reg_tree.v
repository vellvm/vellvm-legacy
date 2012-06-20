Require Import vellvm.
Require Import Kildall.
Require Import ListSet.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import primitives.
Require Import dom_tree.
Require Import dom_set_tree.
Require Import iter_pass.
Require Import pass_combinators.
Require Import vmem2reg.

(*********************************************************************)
(* A algorithm based on dom-tree traversal, and not verified         *)

Record vmap := mkVMap {
  alloca: value;
  others: AssocList value
}.

Definition vm_subst_cmd (vm:vmap) (c:cmd) :=
List.fold_right
  (fun elt c' => let '(id0, v0) := elt in subst_cmd id0 v0 c')
  c vm.(others).

Definition vm_subst_tmn (vm:vmap) (tmn:terminator) :=
List.fold_right
  (fun elt tmn' => let '(id0, v0) := elt in subst_tmn id0 v0 tmn')
  tmn vm.(others).

Definition vm_subst_phi (vm:vmap) (pn:phinode) :=
List.fold_right
  (fun elt pn' => let '(id0, v0) := elt in subst_phi id0 v0 pn')
  pn vm.(others).

Definition vm_get_alloca (vm:vmap): value := vm.(alloca).

Definition vm_set_others (vm:vmap) id0 v0: vmap :=
mkVMap vm.(alloca) (ATree.set id0 v0 vm.(others)).

Definition vm_set_alloca (vm:vmap) v0: vmap :=
mkVMap v0 vm.(others).

Definition ssa_renaming_cmd (c:cmd) (pid:id) (vm: vmap): option cmd * vmap :=
let c' := vm_subst_cmd vm c in
match c' with
| insn_load id0 _ (value_id qid) _ =>
    if (id_dec pid qid) then (None, vm_set_others vm id0 (vm_get_alloca vm))
    else (Some c', vm)
| insn_store _ _ v0 (value_id qid) _ =>
    if (id_dec pid qid) then (None, vm_set_alloca vm v0)
    else (Some c', vm)
| _ => (Some c', vm)
end.

Fixpoint ssa_renaming_cmds (cs:cmds) (pid:id) (vm: vmap) : cmds * vmap :=
match cs with
| nil => (nil, vm)
| c :: cs' =>
    let '(optc0, vm0) := ssa_renaming_cmd c pid vm in
    let '(cs1, vm1) := ssa_renaming_cmds cs' pid vm0 in
    (match optc0 with
     | Some c0 => c0::cs1
     | None => cs1
     end, vm1)
end.

Definition vm_subst_value (vm:vmap) (v:value) :=
List.fold_right
  (fun elt v' => let '(id0, v0) := elt in subst_value id0 v0 v')
  v vm.(others).

Fixpoint ssa_renaming_phis_operands (l0:l) (ps:phinodes) (pid:id)
  (newpids:list id) (vm: vmap) : phinodes :=
match ps with
| nil => nil
| insn_phi id0 t0 vls :: ps' =>
    (if (id_dec id0 pid) || (in_dec id_dec id0 newpids) then
      insn_phi id0 t0
      (List.map
        (fun p : value * l =>
          let '(v1, l1) := p in
               (if (l_dec l0 l1)
                then vm_get_alloca vm
                else v1, l1)) vls)
    else insn_phi id0 t0
          (List.map
            (fun p : value * l =>
              let '(v1, l1) := p in
               (if (l_dec l0 l1)
                then vm_subst_value vm v1
                else v1, l1)) vls))::
    ssa_renaming_phis_operands l0 ps' pid newpids vm
end.

Definition block_subst (f:fdef) (l0:l) (b0:block) : fdef :=
let '(fdef_intro fh bs) := f in
fdef_intro fh
  (List.map (fun b =>
             let '(block_intro l1 _ _ _) := b in
             if (l_dec l1 l0) then b0 else b) bs).

Definition ssa_renaming_succ_phis (f:fdef) (lcur:l) (succ:list l) (pid:id)
  (newpids:list id) (vm:vmap): fdef :=
List.fold_left
  (fun acc lnext =>
   match lookupBlockViaLabelFromFdef acc lnext with
   | None => acc
   | Some (block_intro _ ps cs tmn) =>
       let ps':= ssa_renaming_phis_operands lcur ps pid newpids vm in
       block_subst acc lnext (block_intro lnext ps' cs tmn)
   end) succ f.

Fixpoint update_vm_by_phis (ps:phinodes) (pid:id) (newpids:list id)
  (vm: vmap) : vmap :=
match ps with
| nil => vm
| insn_phi id0 t0 vls :: ps' =>
    if (in_dec id_dec id0 newpids) then vm_set_alloca vm (value_id id0)
    else update_vm_by_phis ps' pid newpids vm
end.

Fixpoint ssa_renaming_dtree (f:fdef) (dt: DTree) (pid:id) (newpids:list id)
  (vm:vmap) : fdef :=
match dt with
| DT_node l0 dts =>
    match lookupBlockViaLabelFromFdef f l0 with
    | None => f
    | Some (block_intro l0 ps cs tmn) =>
        let ps' := List.map (vm_subst_phi vm) ps in
        let vm1 := update_vm_by_phis ps pid newpids vm in
        let '(cs', vm2) := ssa_renaming_cmds cs pid vm1 in
        let tmn' := vm_subst_tmn vm2 tmn in
        let f2 := block_subst f l0 (block_intro l0 ps' cs' tmn') in
        let f3 :=
          ssa_renaming_succ_phis f2 l0
            (successors_terminator tmn) pid newpids vm2 in
        ssa_renaming_dtrees f3 dts pid newpids vm2
    end
end
with ssa_renaming_dtrees (f:fdef) (dts: DTrees) (pid:id)(newpids:list id)
  (vm:vmap) : fdef :=
match dts with
| DT_nil => f
| DT_cons dt dts' =>
    let f' := ssa_renaming_dtree f dt pid newpids vm in
    ssa_renaming_dtrees f' dts' pid newpids vm
end.

Definition vm_init (ty:typ) :=
  mkVMap (value_const (const_undef ty)) (ATree.empty value).

Definition ssa_renaming (f:fdef) (dt:DTree) (pid:id) (ty:typ)
  (newpids:list id) : fdef:=
let f1 := ssa_renaming_dtree f dt pid newpids (vm_init ty) in
if used_in_fdef pid f1 then f1 else remove_fdef pid f1.

Definition insert_phis (f:fdef) (rd:list l) (pid:id) (ty:typ): fdef * list id :=
let preds := XATree.make_predecessors (successors f) in
let '(fdef_intro fh bs) := f in
let ex_ids := getFdefLocs f in
let '(bs', _, newpids) :=
  (List.fold_left
    (fun acc b =>
       let '(bs', ex_ids', newpids) := acc in
       let '(block_intro l0 ps cs tmn) := b in
       match ATree.get l0 preds with
       | Some ((_ :: _) as pds) =>
           let '(exist pid' _) := AtomImpl.atom_fresh_for_list ex_ids' in
           (block_intro l0
             (insn_phi pid' ty
               (fold_left
                  (fun acc p =>
                    ((if In_dec l_dec p rd then value_id pid
                      else value_const (const_undef ty)), p) :: acc)
                   pds nil)::ps)
             cs tmn::bs', pid'::ex_ids', pid'::newpids)
       | _ => (b::bs', ex_ids', newpids)
       end) (List.rev bs) (nil, ex_ids, nil)) in
(fdef_intro fh bs', newpids).

Definition mem2reg_fdef_iter (f:fdef) (dt:DTree) (rd:list l) (dones:list id)
  : fdef * bool * list id :=
match getEntryBlock f with
| Some (block_intro _ _ cs _) =>
    match find_promotable_alloca f cs dones with
    | None => (f, false, dones)
    | Some (pid, ty, num, al) =>
        let '(f', newpids) := insert_phis f rd pid ty in
        (ssa_renaming f' dt pid ty newpids, true, pid::dones)
    end
| _ => (f, false, dones)
end.

Definition mem2reg_fdef_step (dt:DTree) (rd:list l) (st:fdef * list id)
  : (fdef * list id) + (fdef * list id) :=
let '(f, dones) := st in
let '(f1, changed1, dones1) := mem2reg_fdef_iter f dt rd dones in
if changed1 then inr _ (f1, dones1) else inl _ (f1, dones1).

Definition mem2reg_fdef (f:fdef) : fdef :=
match getEntryBlock f, reachablity_analysis f with
| Some (block_intro root _ cs _), Some rd =>
  if print_reachablity rd then
    let '(f1, _) :=
      let b := bound_fdef f in
      let dts := AlgDom.sdom f in
      let chains := compute_sdom_chains dts rd in
      let dt :=
        fold_left
          (fun acc elt =>
           let '(_, chain):=elt in
           create_dtree_from_chain eq_atom_dec acc chain)
          chains (DT_node root DT_nil) in
      if print_dominators b dts && print_adtree dt then
         SafePrimIter.iterate _ (mem2reg_fdef_step dt rd) (f, nil)
      else (f, nil)
    in
    if does_phi_elim tt 
    then fst (IterationPass.iter ElimPhi tt rd f1) else f1
  else f
| _, _ => f
end.

(* the top entry *)
Definition run (m:module) : module :=
let '(module_intro los nts ps) := m in
module_intro los nts
  (List.map (fun p =>
             match p with
             | product_fdef f => product_fdef (mem2reg_fdef f)
             | _ => p
             end) ps).

