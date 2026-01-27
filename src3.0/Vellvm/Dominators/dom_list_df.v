Require Import Coqlib.
Require Import Maps.
Require Import syntax.
Require Import infrastructure.
Require Import dom_tree.
Require Import dom_list.
Require Import dom_list_tree.
Require Import dom_libs.
Require Import dfs.
Require Import push_iter.
Import LLVMsyntax.
Import LLVMinfra.

(* This file constructs domination frontiers. 

  We follow an algorithm that approaches the problem from the opposite direction,
  and tends to run faster than Cytron et al.’s algorithm in practice. The 
  algorithm is based on three observations. First, nodes in a dominance frontier 
  represent join points in the graph, nodes into which control flows from 
  multiple predecessors. Second, the predecessors of any join point, j, must have
  j in their respective dominancefrontier sets, unless the predecessor dominates 
  j. This is a direct result of the defnition of dominance frontiers, above. 
  Finally, the dominators of j’s predecessors must themselves have j in their 
  dominance frontier sets unless they also dominate j.

  These observations lead to a simple algorithm. First, we identify each join 
  point, j—any node with more than one incoming edge is a join point. We then 
  examine each predecessor, p, of j and walk up the dominator tree starting at p. 
  We stop the walk when we reach j’s immediate dominator—j is in the dominance 
  frontier of each of the nodes in the walk, except for j’s immediate dominator. 
  Intuitively, all of the rest of j’s dominators are shared by j’s predecessors 
  as well. Since they dominate j, they will not have j in their dominance 
  frontiers.

  This approach tends to run faster than Cytron et al..’s algorithm in practice, 
  almost certainly for two reasons. First, the iterative algorithm has already 
  built the dominator tree. Second, the algorithm uses no more comparisons than 
  are strictly necessary. Section 9.5.2 will revisit the implementation of the 
  algorithm. *)
Definition idom_of (dts: PMap.t LDoms.t) (p:positive) : option positive :=
match PMap.get p dts with
| Some (idom::_) => Some idom
| _ => None
end.

Definition doms_of (dts: PMap.t LDoms.t) (p:positive) : list positive :=
match PMap.get p dts with
| Some sdoms => p::sdoms
| _ => nil
end.

(* given curr, idom is the immediate dom of curr, and 
   ps doms curr's predecesssors *)
Fixpoint who_has_dom_frontier_aux (curr idom:positive) 
  (acc:PTree.t (list positive)) (ps:list positive) : PTree.t (list positive) :=
match ps with
| nil => acc
| p::ps' =>
  if (positive_eq_dec idom p) then acc 
  else who_has_dom_frontier_aux curr idom (PTree.set p (curr::acc???p) acc) ps'
end.

(* given curr, idom is the immediate dom of curr, and 
   pred is one of curr's predecesssors *)
Definition who_has_dom_frontier (dts: PMap.t LDoms.t) (curr idom:positive)
  (acc:PTree.t (list positive)) (pred:positive) : PTree.t (list positive) :=
who_has_dom_frontier_aux curr idom acc (doms_of dts pred).

Definition pdom_frontier_fun (dts: PMap.t LDoms.t) (acc:PTree.t (list positive)) 
  (p:positive) (preds: list positive) : PTree.t (list positive) :=
match preds with
| p1::p2::_ => 
  match idom_of dts p with
  | None => acc
  | Some idom => fold_left (who_has_dom_frontier dts p idom) preds acc
  end
| _ => acc
end.

Definition pdom_frontier (ppreds: PTree.t (list positive)) 
  (dts: PMap.t LDoms.t) : PTree.t (list positive) :=
PTree.fold (pdom_frontier_fun dts) ppreds (PTree.empty _).

Definition dom_frontier (f: fdef) (gen_tree: bool) 
  : ATree.t (list l) * option DTree :=
  let asuccs := cfg.successors f in
  match LLVMinfra.getEntryLabel f with
  | Some le =>
      let '(mkPO _ a2p) := dfs asuccs le 1%positive in
      let psuccs := asuccs_psuccs a2p asuccs in
      match ATree.get le a2p with
      | Some pe => 
         let dts := pdom_analyze psuccs pe (num_iters f) in
         let ppreds := XPTree.make_predecessors psuccs in
         let dfs := pdom_frontier ppreds dts in
         let p2a := a2p_p2a a2p in
         let odt :=
           if gen_tree then
             let res := fun p:positive => PMap.get p dts in
             let pdt := create_dtree pe (get_reachable_nodes (bound_fdef f) a2p) res in
             DTreeConv.sdtree_tdtree p2a pdt
           else None in
         let df := PTree.fold 
           (fun acc p0 df0 => 
            match p2a ? p0 with
            | None => acc
            | Some a0 => ATree.set a0 (ps2as p2a df0) acc
            end) dfs (ATree.empty _) in
         (df, odt)
      | None => (ATree.empty _, None)
      end
  | None => (ATree.empty _, None)
  end.

