Require Import vellvm.
Require Import Maps.
Require Import Iteration.
Require Import primitives.
Require Import dom_tree.
Require Import iter_pass.
Require Import pass_combinators.
Require Import vmem2reg.
Require Import vmem2reg_opt.
Require Import dom_list_df.

Record IDFstate := mkIDFst {
  IDFwrk : list id;
  IDFphi : AVLMap.t unit
}.

Definition IDFstep (defs : AVLMap.t unit) (dfs : ATree.t (list id)) 
  (st : IDFstate) : AVLMap.t unit + IDFstate :=
match IDFwrk st with
| nil => inl (IDFphi st)
| pick::wrk' =>
    match dfs ! pick with
    | Some df =>
        inr (fold_left (fun acc d => 
                        match AVLMap.find _ d (IDFphi st) with
                        | None =>
                            mkIDFst 
                              (match AVLMap.find _ d defs with
                               | None => d :: IDFwrk acc
                               | _ => IDFwrk acc
                               end)
                              (AVLMap.add _ d tt (IDFphi acc))
                        | Some _ => acc
                        end) df (mkIDFst wrk' (IDFphi st)))
    | _ => inr (mkIDFst wrk' (IDFphi st))
    end
end.

Definition IDF (defs : AVLMap.t unit) (dfs : ATree.t (list id)) :=
  PrimIter.iterate _ _ (IDFstep defs dfs) 
    (mkIDFst 
       (AVLMap.fold (fun acc elt => fst elt :: acc) defs nil) AVLMap.empty).

(*********************************************************************)
(*  The following functions check if an alloca is legal to promote *)
Definition is_promotable_cmd pid :=
  (fun acc0 c =>
          if used_in_cmd pid c then
            match c with
            | insn_load _ _ _ _ => acc0
            | insn_store _ _ v _ _ => 
                let flag := negb (valueEqB v (value_id pid)) in
                (flag && fst acc0, flag || snd acc0)
            | _ => (false, snd acc0)
            end
          else acc0).

Definition is_promotable_fun pid :=
  (fun acc b =>
     let '(l0, stmts_intro ps cs tmn) := b in
     if (List.fold_left (fun re p => re || used_in_phi pid p) ps
          (used_in_tmn pid tmn)) then (false, snd acc)
     else
       let '(promotable, defined) := 
         fold_left (is_promotable_cmd pid) cs (fst acc, false) in
       if defined then (promotable, AVLMap.add _ l0 tt (snd acc)) 
       else (promotable, snd acc)
  ).

Definition is_promotable (f:fdef) (le:l) (pid:id) : bool * AVLMap.t unit :=
let '(fdef_intro _ bs) := f in
fold_left (is_promotable_fun pid) bs (true, AVLMap.add _ le tt AVLMap.empty).

Fixpoint find_promotable_alloca (f:fdef) (le:l) (cs:cmds) (dones:list id)
  : option (id * typ * value * align * AVLMap.t unit) :=
match cs with
| nil => None
| insn_alloca pid ty num al :: cs' =>
    if negb (In_dec id_dec pid dones)
    then 
      let '(promotable, defs) := is_promotable f le pid in
      if promotable then Some (pid, ty, num, al, defs)
      else find_promotable_alloca f le cs' dones
    else find_promotable_alloca f le cs' dones
| _ :: cs' => find_promotable_alloca f le cs' dones
end.

(*********************************************************************)

Fixpoint needs_load (inserts: AVLMap.t unit) (scs: (list l)) : bool :=
match scs with
| nil => false
| sc::scs' =>
  match AVLMap.find _ sc inserts with
  | Some _ => true
  | None => needs_load inserts scs'
  end
end.

Definition gen_fresh_ids (succs:AVLMap.t (list l)) (rd:list id) 
  (inserts: AVLMap.t unit) (ex_ids:list atom)
  : ((AVLMap.t (option id * option (id * id))) * list atom) :=
  List.fold_left
    (fun acc l0 =>
       let '(nids', ex_ids') := acc in
       let '(exist lid' _) := AtomImpl.atom_fresh_for_list ex_ids' in
       let '(exist pid' _) := AtomImpl.atom_fresh_for_list (lid'::ex_ids') in
       let '(exist sid' _) :=
         AtomImpl.atom_fresh_for_list (pid'::lid'::ex_ids') in    
       let opsid :=
         match AVLMap.find _ l0 inserts with
         | Some _ => Some (pid', sid')
         | None => None
         end in
       let olid := 
         match AVLMap.find _ l0 succs with
         | None => None
         | Some scs => if needs_load inserts scs then Some lid' else None
         end in
       (AVLMap.add _ l0 (olid, opsid) nids', sid'::pid'::lid'::ex_ids')
    ) rd (AVLMap.empty, ex_ids).

Definition gen_phinode (pid':id) (ty:typ) 
  (nids:AVLMap.t (option id* option (id*id))) (pds:list l) : phinode :=
  insn_phi pid' ty
    (fold_left
       (fun acc p =>
            ((match AVLMap.find _ p nids with
             | Some (Some lid0, _) => value_id lid0
             | _ => value_const (const_undef ty)
             end), p) :: acc)
        pds nil).

Definition phinodes_placement_block (pid:id) (ty:typ) (al:align)
  (nids:AVLMap.t (option id* option (id*id))) 
  (preds:AVLMap.t (list l)) (b:block) : block :=
  let '(l0, stmts_intro ps cs tmn) := b in
  match AVLMap.find _ l0 nids with
  | Some (olid, opsid) =>
    let cs' :=
      match olid with
      | Some lid => [insn_load lid ty (value_id pid) al]
      | _ => nil
      end in
    match opsid, AVLMap.find _ l0 preds with
    | Some (pid', sid), Some ((_ :: _) as pds) =>
        (l0, stmts_intro
          ((gen_phinode pid' ty nids pds)::ps)
          (insn_store sid ty (value_id pid') (value_id pid) al::
           cs ++ cs') tmn)
    | _, _ => (l0, stmts_intro ps (cs ++ cs') tmn)
    end
 | _ => b
 end.

Definition phinodes_placement_blocks (pid:id) (ty:typ) (al:align)
  (nids:AVLMap.t (option id*option (id*id))) (preds:AVLMap.t (list l)) 
  (bs:blocks): blocks:=
List.map (phinodes_placement_block pid ty al nids preds) bs.

Definition phinodes_placement (rd:list l) (inserts: AVLMap.t unit) 
  (pid:id) (ty:typ) (al:align) (succs preds:AVLMap.t (list l)) (f:fdef) : fdef :=
let '(fdef_intro fh bs) := f in
let '(nids, _) := gen_fresh_ids succs rd inserts (getFdefLocs f) in
let bs1 := phinodes_placement_blocks pid ty al nids preds bs in
fdef_intro fh bs1.

(************************************************)

Inductive CsDTree : Set :=
| CsDT_node : id -> cmds -> CsDTrees -> CsDTree
with CsDTrees : Set :=
| CsDT_nil : CsDTrees
| CsDT_cons : CsDTree -> CsDTrees -> CsDTrees
.

Definition block_list_2_cmds_map (bs: blocks) : AVLMap.t cmds :=
fold_left (fun acc b => 
           let '(l0, stmts_intro _ cs0 _) := b in 
           AVLMap.add _ l0 cs0 acc) bs AVLMap.empty.

Fixpoint DTree_2_CsDTree (csmap: AVLMap.t cmds) (dt: @DTree id) : option CsDTree :=
match dt with
| DT_node id0 dts =>
    match AVLMap.find _ id0 csmap, DTrees_2_CsDTrees csmap dts with
    | Some cs0, Some csdts => Some (CsDT_node id0 cs0 csdts)
    | _, _ => None
    end
end
with DTrees_2_CsDTrees (csmap: AVLMap.t cmds) (dts: DTrees) : option CsDTrees :=
match dts with
| DT_nil => Some CsDT_nil
| DT_cons dt dts' =>
    match DTree_2_CsDTree csmap dt, DTrees_2_CsDTrees csmap dts' with
    | Some csdt, Some csdts' => Some (CsDT_cons csdt csdts')
    | _, _ => None
    end
end.

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

Definition find_stld_pairs_cmds (pid:id) (acc:stld_state * AssocList action) 
  (cs:cmds) : stld_state * AssocList action :=
List.fold_left (find_stld_pair_cmd pid) cs acc.

Fixpoint find_stld_pairs_CsDTree (pid:id) (acc:stld_state * AssocList action) 
  (cdt:CsDTree) : stld_state * AssocList action :=
match cdt with
| CsDT_node _ cs cdts => 
    find_stld_pairs_CsDTrees pid (find_stld_pairs_cmds pid acc cs) cdts
end
with find_stld_pairs_CsDTrees (pid:id) (acc:stld_state * AssocList action) 
  (cdts:CsDTrees) : stld_state * AssocList action :=
match cdts with
| CsDT_nil => acc
| CsDT_cons cdt cdts' =>
    let '(_, acs) := find_stld_pairs_CsDTree pid acc cdt in
    find_stld_pairs_CsDTrees pid (fst acc, acs) cdts'
end.

Definition elim_stld_fdef (pid:id) (dt:DTree) (f:fdef) : fdef :=
let '(fdef_intro _ bs) := f in
let csmap := block_list_2_cmds_map bs in
match DTree_2_CsDTree csmap dt with
| Some cdt =>
    let pairs := rev (snd (find_stld_pairs_CsDTree pid (STLD_init, nil) cdt)) in
    AVLComposedPass.run pairs f
| None => f
end.

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
  (dfs : ATree.t (list id)) (dt:DTree) 
  (succs preds:AVLMap.t (list l)) (dones:list id) : fdef * bool * list id := 
match getEntryBlock f with
| Some (le, stmts_intro _ cs _) =>
    match find_promotable_alloca f le cs dones with
    | None => (f, false, dones)
    | Some (pid, ty, num, al, defs) =>
       match IDF defs dfs with
       | Some inserts =>
          ((seq_trans
             (phinodes_placement rd inserts pid ty al succs preds)
           (seq_trans
             (cond_trans
               (fun _ => does_stld_elim tt)
               (elim_stld_fdef pid dt)
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
      | _ => (f, false, dones)
      end
    end
| _ => (f, false, dones)
end.

(************************************************)
(* one step of macro-optimization, after each step, we check if
   anything was changed, if not, we stop.
   return a sum: left means unfinished; right means done
*)
Definition macro_mem2reg_fdef_step (rd:list l) 
  (dfs : ATree.t (list id)) (dt:DTree) (succs preds:AVLMap.t (list l))
  (st:fdef * list id) : (fdef * list id) + (fdef * list id) :=
let '(f, dones) := st in
let '(f1, changed1, dones1) :=
      macro_mem2reg_fdef_iter f rd dfs dt succs preds dones in
if changed1 then inr _ (f1, dones1) else inl _ (f1, dones1).

(************************************************)

Fixpoint successors_blocks (bs: blocks) : AVLMap.t ls :=
match bs with
| nil => AVLMap.empty
| (l0, stmts_intro _ _ tmn) :: bs' =>
    AVLMap.add _ l0 (successors_terminator tmn) (successors_blocks bs')
end.

Definition successors (f: fdef) : AVLMap.t ls :=
let '(fdef_intro _ bs) := f in
successors_blocks bs.

Fixpoint add_successors (pred: AVLMap.t (list id))
                        (from: id) (tolist: list id)
                        {struct tolist} : AVLMap.t (list id) :=
match tolist with
| nil => pred
| hd :: rem => 
  let old := match AVLMap.find _ hd pred with
             | Some re => re
             | _ => nil
             end in
  add_successors (AVLMap.add _ hd (from :: old) pred) from rem
end.

Definition make_predecessors (succs: AVLMap.t ls) : AVLMap.t (list id) :=
  AVLMap.fold (fun x y => add_successors x (fst y) (snd y)) succs AVLMap.empty.

(************************************************)

Definition elim_phi_phi (f:fdef) acc (pn:phinode): AssocList action :=
let '(insn_phi pid _ vls) := pn in 
if does_dead_phi_elim tt then
  if used_in_fdef pid f then acc else (pid, AC_remove)::acc
else acc.

Definition elim_phi_phis f ps : AssocList action :=
List.fold_left (elim_phi_phi f) ps nil.

Definition elim_phi_block f (b:block) :=
let '(l5, stmts_intro ps cmds5 terminator5) := b in
elim_phi_phis f ps.

Definition elim_phi_fdef f :=
let '(fdef_intro fh bs) := f in
List.flat_map (elim_phi_block f) bs.

Definition elim_phi_step f :=
match elim_phi_fdef f with
| nil => inl f
| pairs => inr (AVLComposedPass.run pairs f)
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
match getEntryBlock f, reachablity_analysis f, dom_frontier f true with
| Some (root, stmts_intro _ cs _), Some rd, (dfs, Some dtree) =>
  if print_reachablity rd then
    let '(f1, _) :=
      let succs := successors f in
      let preds := make_predecessors succs in
      SafePrimIter.iterate _ 
        (macro_mem2reg_fdef_step rd dfs dtree succs preds) (f, nil) 
      in
    if does_phi_elim tt 
    then SafePrimIter.iterate _ elim_phi_step f1 else f1
  else f
| _, _, _ => f
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



