Require Export Coqlib.
Require Export Iteration.
Require Export Maps.
Require Import syntax.
Require Import infrastructure_props.
Require Import Metatheory.
Require Import Program.Tactics.
Require Import dom_libs.
Require Import dfs.

Module Weak_Pred_Dataflow_Solver (NS: PNODE_SET) (L: LATTICEELT).

Section Kildall.

Variable successors: PTree.t (list positive).
Variable predecessors: PTree.t (list positive).
Variable transf : positive -> L.t -> L.t.
Variable entrypoints: list (positive * L.t).

(** The state of the iteration has two components:
- A mapping from program points to values of type [L.t] representing
  the candidate solution found so far.
- A worklist of program points that remain to be considered.
*)

Record state : Type :=
  mkstate { st_in: PMap.t L.t; st_wrk: NS.t }.

(** Kildall's algorithm, in pseudo-code, is as follows:
<<
    while st_wrk is not empty, do
        extract a node n from st_wrk
        compute in = st_in[n]
        for each predecessor p of n:
            compute out = transf p st_in[p]
            compute in := lub in out
        end for
        if in <> st_in[n]:
            st_in[n] := in
            st_wrk := st_wrk union {successors of n}
        end if
    end while
    return st_in
>>

The initial state is built as follows:
- The initial mapping sets all program points to [L.bot], except
  those mentioned in the [entrypoints] list, for which we take
  the associated approximation as initial value.  Since a program
  point can be mentioned several times in [entrypoints], with different
  approximations, we actually take the l.u.b. of these approximations.
- The initial worklist contains all the program points. *)

Fixpoint start_state_in (ep: list (positive * L.t)) : PMap.t L.t :=
  match ep with
  | nil =>
      PMap.init L.bot
  | (n, v) :: rem =>
      let m := start_state_in rem in PMap.set n (L.lub m ?? n v) m
  end.

Definition start_state :=
  mkstate (start_state_in entrypoints) (NS.initial predecessors).

(** [propagate_pred_list] corresponds, in the pseudocode,
  to the [for] loop iterating over all predecessors. *)

Definition propagate_pred_list (s: state) (oldl: L.t) (preds: list positive) 
  : L.t :=
fold_left (fun acc p => L.lub acc (transf p s.(st_in) ?? p)) preds oldl.

(** [step] corresponds to the body of the outer [while] loop in the
  pseudocode. *)

Definition add_successors_into_worklist (rem: NS.t) (n: positive) : NS.t :=
fold_left (fun acc s => NS.add n acc) (successors ??? n) rem.

Definition step (s: state) : PMap.t L.t + state :=
  match NS.pick s.(st_wrk) with
  | None =>
      inl _ s.(st_in)
  | Some(n, rem) =>
      let oldl := s.(st_in) ?? n in
      let newl := propagate_pred_list s oldl (predecessors ??? n) in
      let s' := 
        if L.beq oldl newl
        then mkstate s.(st_in) rem
        else mkstate (PMap.set n newl s.(st_in)) 
               (add_successors_into_worklist rem n) in
      inr _ s'
  end.

(** The whole fixpoint computation is the iteration of [step] from
  the start state. *)

Definition fixpoint : option (PMap.t L.t) :=
  PrimIter.iterate _ _ step start_state.

End Kildall.

End Weak_Pred_Dataflow_Solver.

Module LDoms := Doms (MergeLt).
Module DomDS := Weak_Pred_Dataflow_Solver (PNodeSetMax) (LDoms).

Definition transfer (n:positive) (input: LDoms.t) : LDoms.t :=
match input with
| None => None
| Some ps => Some (n::ps)
end.

Require analysis.
Require Import infrastructure.
Import LLVMsyntax.

Definition dom_analyze (f: fdef) : PMap.t LDoms.t :=
  let asuccs := analysis.successors f in
  match LLVMinfra.getEntryBlock f with
  | Some (block_intro le _ _ _) =>
      let 'mkPO _ a2p := dfs asuccs le 1%positive in
      let psuccs := asuccs_psuccs a2p asuccs in
      match ATree.get le a2p with
      | Some pe => 
        match DomDS.fixpoint psuccs
                (XPTree.make_predecessors psuccs) 
                transfer ((pe, LDoms.top) :: nil) with
        | None => (PMap.set pe LDoms.top (PMap.init LDoms.bot))
        | Some res => res
        end
      | None => PMap.init LDoms.bot
      end
  | None => PMap.init LDoms.bot
  end.


