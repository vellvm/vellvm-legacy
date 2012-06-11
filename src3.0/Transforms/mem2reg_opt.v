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
Require Import mem2reg.

(************************************************)

Fixpoint map_filter (A:Type) (cond: A -> bool) (f: A -> A) (l1: list A) 
  : list A :=
match l1 with
| nil => nil
| x::l0 => 
    if cond x then f x::(map_filter A cond f l0) else map_filter A cond f l0
end.

Implicit Arguments map_filter [A].

Definition subst_remove_block id' v' b :=
let '(block_intro l0 ps0 cs0 tmn0) := b in
block_intro l0
  (map_filter 
     (fun p => negb (id_dec (getPhiNodeID p) id')) (subst_phi id' v') ps0)
  (map_filter 
     (fun c => negb (id_dec (getCmdLoc c) id')) (subst_cmd id' v') cs0) 
  (subst_tmn id' v' tmn0).

Definition subst_remove_fdef id' v' f :=
let '(fdef_intro fh bs) := f in
fdef_intro fh (List.map (subst_remove_block id' v') bs).

(************************************************)

Inductive stld_state : Set :=
| STLD_init : stld_state
| STLD_store : id -> value -> stld_state
| STLD_alloca : typ -> stld_state
.

Inductive action : Set :=
| AC_remove: action
| AC_vsubst: value -> action
| AC_tsubst: typ -> action
.

Definition subst_actions (id0:id) (v0:value) (pairs: AssocList action) :
  AssocList action :=
List.map 
  (fun elt => 
   match elt with
   | (id1, AC_vsubst v1) => (id1, AC_vsubst (subst_value id0 v0 v1))
   | _ => elt
   end) pairs.

Fixpoint substs_actions (pairs: AssocList action) : AssocList action :=
match pairs with 
| nil => nil
| (id1, AC_vsubst v1)::pairs' => 
    (id1, AC_vsubst v1)::subst_actions id1 v1 (substs_actions pairs')
| (id1, AC_tsubst t1)::pairs' => 
    (id1, AC_tsubst t1)::
      subst_actions id1 (value_const (const_undef t1)) (substs_actions pairs')
| elt::pairs' => elt::substs_actions pairs'
end.

Definition apply_action (f:fdef) (elt:id * action): fdef :=
let '(id1, ac1) := elt in
match ac1 with
| AC_vsubst v1 => subst_remove_fdef id1 v1 f
| AC_tsubst t1 => 
    subst_remove_fdef id1 (value_const (const_undef t1)) f
| AC_remove => remove_fdef id1 f
end.

Definition apply_actions (f:fdef) (pairs: AssocList action) : fdef :=
List.fold_left apply_action (substs_actions pairs) f.

(************************************************)

Definition find_stld_pair_cmd (pid:id) (acc:stld_state * AssocList action) 
  (c:cmd) : stld_state * AssocList action :=
let '(st, actions) := acc in
match c with
| insn_alloca qid ty value5 align5 =>
    if id_dec pid qid
    then (STLD_alloca ty, actions)
    else acc
| insn_store sid typ5 v0 value2 align5 =>
    match value2 with
    | value_id qid =>
       if id_dec pid qid
       then 
         match st with
         | STLD_store sid' _ => (STLD_store sid v0, (sid', AC_remove)::actions)
         | _ => (STLD_store sid v0, actions)
         end
      else acc
    | value_const const5 => acc
    end
| insn_load lid typ5 value1 align5 =>
    match value1 with
    | value_id qid =>
       if id_dec pid qid
       then 
         match st with
         | STLD_store _ v' => (st, (lid, AC_vsubst v')::actions)
         | STLD_alloca ty' => (st, (lid, AC_tsubst ty')::actions)
         | _ => acc
         end
       else acc
    | value_const const5 => acc
    end
| _ => acc
end.

Definition find_stld_pairs_cmds (cs:cmds) (pid:id) : AssocList action :=
snd (List.fold_left (find_stld_pair_cmd pid) cs (STLD_init, nil)).

Definition find_stld_pairs_block (pid:id) (b:block) : AssocList action :=
let '(block_intro l5 phinodes5 cs terminator5) := b in
find_stld_pairs_cmds cs pid.

Definition elim_stld_fdef (pid:id) (f:fdef) : fdef :=
let '(fdef_intro _ bs) := f in
let pairs := List.flat_map Datatypes.id (List.map (find_stld_pairs_block pid) bs) in
apply_actions f pairs.

(************************************************)
(* in function [f], given its reachable blocks [rd], CFG represented by
   successors [succs] and predecessors [preds]. Do the following in sequence
   1) find a promotable alloca
   2) insert phinodes
   3) las/laa/sas
   4) dse
   5) dae
   [dones] tracks the allocas checked and seen
*)
Definition macro_mem2reg_fdef_iter (f:fdef) (rd:list l) 
  (succs preds:ATree.t (list l)) (dones:list id) : fdef * bool * list id := 
match getEntryBlock f with
| Some (block_intro _ _ cs _) =>
    match find_promotable_alloca f cs dones with
    | None => (f, false, dones)
    | Some (pid, ty, num, al) =>
       ((seq_trans
          (phinodes_placement rd pid ty al succs preds)
        (seq_trans
          (cond_trans
            (fun _ => does_stld_elim tt)
            (elim_stld_fdef pid)
            (@Datatypes.id fdef))
        (seq_trans
          (cond_trans
            (load_in_fdef pid)
            (@Datatypes.id fdef)  
            (elim_dead_st_fdef pid))
          (cond_trans
            (used_in_fdef pid)
            (@Datatypes.id fdef)
            (remove_fdef pid))))) f, true, pid::dones)
    end
| _ => (f, false, dones)
end.

(************************************************)
(* one step of macro-optimization, after each step, we check if
   anything was changed, if not, we stop.
   return a sum: left means unfinished; right means done
*)
Definition macro_mem2reg_fdef_step (rd:list l) (succs preds:ATree.t (list l))
  (st:fdef * list id) : (fdef * list id) + (fdef * list id) :=
let '(f, dones) := st in
let '(f1, changed1, dones1) :=
      macro_mem2reg_fdef_iter f rd succs preds dones in
if changed1 then inr _ (f1, dones1) else inl _ (f1, dones1).

(************************************************)

Definition elim_phi_phi (f:fdef) acc (pn:phinode): AssocList action :=
let '(insn_phi pid _ vls) := pn in 
let ndpvs := 
  remove_redundancy nil (value_id pid::List.map fst vls) 
in
match ndpvs with
| value_id id1 as v1::v2::nil =>
    if (id_dec pid id1) then 
      (* if v1 is pid, then v2 cannot be pid*)
      (pid, AC_vsubst v2)::acc
    else  
      (* if v1 isnt pid, then v2 must be pid*)
      (pid, AC_vsubst v1)::acc
| value_const _ as v1::_::nil =>
    (* if v1 is const, then v2 must be pid*)
   (pid, AC_vsubst v1)::acc
| v1::nil => 
    (* v1 must be pid, so pn:= pid = phi [pid, ..., pid] *)
    (pid, AC_remove)::acc
| _ => 
   if does_dead_phi_elim tt then
      if used_in_fdef pid f then acc else (pid, AC_remove)::acc
   else acc
end.

Definition elim_phi_phis f ps : AssocList action :=
List.fold_left (elim_phi_phi f) ps nil.

Definition elim_phi_block f b :=
let '(block_intro l5 ps cmds5 terminator5) := b in
elim_phi_phis f ps.

Definition elim_phi_fdef f :=
let '(fdef_intro fh bs) := f in
List.flat_map Datatypes.id (List.map (elim_phi_block f) bs).

Definition elim_phi_step f :=
match elim_phi_fdef f with
| nil => inl f
| pairs => inr (apply_actions f pairs)
end.

(************************************************)
(* The two kinds of mem2reg algorithm for each function
   1) when does_macro_m2r tt = true
      A pipelined algorithm based on a group of primitives, which is
      fully verified.
   2) when does_macro_m2r tt = false
      A algorithm based on dom-tree traversal, and not verified
*)
Definition mem2reg_fdef (f:fdef) : fdef :=
match getEntryBlock f, reachablity_analysis f with
| Some (block_intro root _ cs _), Some rd =>
  if print_reachablity rd then
    let '(f1, _) :=
      let succs := successors f in
      let preds := XATree.make_predecessors succs in
      SafePrimIter.iterate _ 
        (macro_mem2reg_fdef_step rd succs preds) (f, nil) 
    in
    if does_phi_elim tt 
    then SafePrimIter.iterate _ elim_phi_step f1 else f1
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



