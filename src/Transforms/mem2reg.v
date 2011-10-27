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
Require Import dtree.
Require Import primitives.
Require Import Maps.

Definition is_promotable (f:fdef) (pid:id) : bool :=
let '(fdef_intro _ bs) := f in
fold_left 
  (fun acc b => 
     let '(block_intro _ _ cs _) := b in
     fold_left 
       (fun acc0 c =>
          if used_in_cmd pid c then
            match c with
            | insn_load _ _ _ _ => acc0
            | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) && acc0
            | _ => false
            end
          else acc0) cs acc
  ) bs true. 

Fixpoint find_promotable_alloca (f:fdef) (cs:cmds) : option (id * typ) :=
match cs with
| nil => None
| insn_alloca pid ty _ _ :: cs' =>
    if is_promotable f pid then Some (pid, ty)
    else find_promotable_alloca f cs'
| _ :: cs' => find_promotable_alloca f cs'
end.

Definition insert_phis (f:fdef) (pid:id) (ty:typ) : fdef :=
let preds := make_predecessors (successors f) in
let '(fdef_intro fh bs) := f in
fdef_intro fh
(List.map
  (fun b =>
     let '(block_intro l0 ps cs tmn) := b in
     match ATree.get l0 preds with
     | Some (_ :: _ :: _ as pds) => 
         block_intro l0 
           (insn_phi pid ty 
             (fold_left (fun acc p => Cons_list_value_l (value_id pid) p acc) 
               pds Nil_list_value_l)::ps) 
           cs tmn
     | _ => b
     end) bs).

Fixpoint ssa_renaming_cmds (f:fdef) (cs:cmds) (pid:id) (pv: value)
  : fdef * value :=
match cs with
| nil => (f, pv)
| c :: cs' =>
    let '(f', pv') :=
      match c with
      | insn_load id0 _ (value_id qid) _ => 
          if (id_dec pid qid) then (remove_fdef id0 (subst_fdef id0 pv f), pv) 
          else (f, pv)
      | insn_store id0 _ v0 (value_id qid) _ => 
          if (id_dec pid qid) then (remove_fdef id0 f, v0) else (f, pv)
      | _ => (f, pv)
      end in
    ssa_renaming_cmds f' cs' pid pv'
end.

Definition subst_phinode_fdef (f:fdef) (l0:l) (id0:id) (pn:phinode) : fdef :=
let '(fdef_intro fh bs) := f in
fdef_intro fh
  (List.map (fun b => 
             let '(block_intro l1 ps cs tmn) := b in
             if (l_dec l0 l1) then
               block_intro l1 
                 (List.map (fun pn' =>
                            let '(insn_phi id1 _ _) := pn' in
                            if (l_dec id0 id1) then pn else pn') ps) cs tmn
             else b
             ) bs).

Fixpoint ssa_renaming_phis_id (f:fdef) (l0:l) (ps:phinodes) (pid:id) (pv:value) 
  (ex_ids:list atom) (newpids:list id): fdef * value * list atom * list id :=
match ps with
| nil => (f, pv, ex_ids, newpids)
| insn_phi id0 t0 vls :: ps' =>
    if (id_dec id0 pid) then
      let '(exist pid' _) := AtomImpl.atom_fresh_for_list ex_ids in
      (subst_phinode_fdef f l0 id0 (insn_phi pid' t0 vls), 
       value_id pid', pid'::ex_ids, pid'::newpids)
    else ssa_renaming_phis_id f l0 ps' pid pv ex_ids newpids
end.

Fixpoint ssa_renaming_phis_operands (f:fdef) (l0:l) (ps:phinodes) (pid:id) 
  (pv:value) (newpids:list id): fdef :=
match ps with
| nil => f
| insn_phi id0 t0 vls :: ps' =>
    if (id_dec id0 pid) || (in_dec id_dec id0 newpids) then
      subst_phinode_fdef f l0 id0 
        (insn_phi id0 t0 
          (make_list_value_l
            (map_list_value_l
              (fun v1 l1 => (if (l_dec l0 l1) then pv else v1, l1)) 
              vls)))
    else ssa_renaming_phis_operands f l0 ps' pid pv newpids
end.

Definition ssa_renaming_succ_phis (f:fdef) (lcur:l) (succ:list l) (pid:id) 
  (pv:value) (newpids:list id): fdef :=
List.fold_left (fun acc lnext =>
                match lookupBlockViaLabelFromFdef acc lnext with
                | None => acc
                | Some (block_intro _ ps _ _) =>
                    ssa_renaming_phis_operands f lcur ps pid pv newpids
                end) succ f.

Fixpoint ssa_renaming_dtree (f:fdef) (dt: DTree) (pid:id) (pv: value) 
  (ex_ids:list atom) (newpids:list id) : fdef * list atom * list id :=
match dt with
| DT_node l0 dts => 
    match lookupBlockViaLabelFromFdef f l0 with
    | None => (f, ex_ids, newpids)
    | Some (block_intro l0 ps cs tmn) =>
        let '(f1, pv1, ex_ids1, newpids1) :=
          ssa_renaming_phis_id f l0 ps pid pv ex_ids newpids in
        let '(f2, pv2) := ssa_renaming_cmds f1 cs pid pv1 in
        let f3 := 
          ssa_renaming_succ_phis f2 l0 
            (successors_terminator tmn) pid pv2 newpids1 in
        ssa_renaming_dtrees f3 dts pid pv2 ex_ids1 newpids1
    end
end
with ssa_renaming_dtrees (f:fdef) (dts: DTrees) (pid:id) (pv: value) 
  (ex_ids:list atom) (newpids:list id) : fdef * list atom * list id :=
match dts with
| DT_nil => (f, ex_ids, newpids)
| DT_cons dt dts' => 
    let '(f', ex_ids', newpids') := 
      ssa_renaming_dtree f dt pid pv ex_ids newpids in
    ssa_renaming_dtrees f' dts' pid pv ex_ids' newpids'
end.

Definition getFdefLocs fdef : ids :=
match fdef with
| fdef_intro (fheader_intro _ _ _ la _) bs => getArgsIDs la ++ getBlocksLocs bs 
end.

Definition ssa_renaming (f:fdef) (dt:DTree) (pid:id) (ty:typ) : fdef := 
let f1 := remove_fdef pid f in
match 
  ssa_renaming_dtree f1 dt pid 
    (value_const (const_undef ty)) (getFdefLocs f1) nil with
| (f2, _, _) => f2
end.

Definition mem2reg_fdef_iter (f:fdef) (dt:DTree) : fdef * bool := 
match getEntryBlock f with
| Some (block_intro _ _ cs _) =>
    match find_promotable_alloca f cs with
    | None => (f, false)
    | Some (pid, ty) => (ssa_renaming (insert_phis f pid ty) dt pid ty, true)
    end
| _ => (f, false)
end.

Definition mem2reg_fdef_step (dt:DTree) (f:fdef) : fdef + fdef :=
let '(f1, changed1) := mem2reg_fdef_iter f dt in
if changed1 then inr _ f1 else inl _ f1.

Definition mem2reg_fdef (f:fdef) : fdef :=
match getEntryBlock f, reachablity_analysis f with
| Some (block_intro root _ cs _), Some rd =>
    let b := bound_fdef f in
    let dts := dom_analyze f in
    let chains := compute_sdom_chains b dts rd in
    let dt :=
      fold_left 
      (fun acc elt => 
        let '(_, chain):=elt in 
        create_dtree_from_chain acc chain) 
      chains (DT_node root DT_nil) in
    if print_reachablity rd && print_dominators b dts && 
       print_dtree dt then
       match 
         fix_temporary_fdef 
           (SafePrimIter.iterate _ (mem2reg_fdef_step dt) f) with
       | Some f' => f'
       | None => f
       end
    else f
| _, _ => f
end.

Definition run (m:module) : module :=
let '(module_intro los nts ps) := m in
module_intro los nts 
  (List.map (fun p =>
             match p with
             | product_fdef f => product_fdef (mem2reg_fdef f)
             | _ => p
             end) ps).

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/Vellvm/monads" "-I" "~/SVN/sol/vol/src/Vellvm/ott" "-I" "~/SVN/sol/vol/src/Vellvm/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-impredicative-set") ***
*** End: ***
 *)
