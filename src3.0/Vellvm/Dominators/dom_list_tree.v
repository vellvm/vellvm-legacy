Require Import Coqlib.
Require Import Maps.
Require Import syntax.
Require Import infrastructure_props.
Require Import Metatheory.
Require Import Program.Tactics.
Require Import push_iter.

Inductive DTree : Set :=
| DT_node : positive -> DTrees -> DTree
with DTrees : Set :=
| DT_nil : DTrees
| DT_cons : DTree -> DTrees -> DTrees
.

Fixpoint list2tree hd tl := 
match tl with
| nil => DT_node hd DT_nil
| hd'::tl' => DT_node hd (DT_cons (list2tree hd' tl') DT_nil)
end.

Fixpoint dtree_insert dt parent child tl : DTree :=
match dt with
| DT_node l0 dts0 =>
    if positive_eq_dec parent l0
    then DT_node l0 (dtrees_insert dts0 child tl)
    else dt
end
with dtrees_insert (dts: DTrees) child tl : DTrees :=
match dts with
| DT_nil => DT_cons (list2tree child tl) DT_nil
| DT_cons dt0 dts0 =>
    let '(DT_node l0 _) := dt0 in
    if positive_eq_dec l0 child then 
      match tl with
      | child'::tl' => DT_cons (dtree_insert dt0 child child' tl') dts0
      | _ => dts
      end
    else DT_cons dt0 (dtrees_insert dts0 child tl)
end.

Fixpoint compute_sdom_chains_aux (res: positive -> LDoms.t)
  (bd: list positive) (acc: list (positive * list positive)) 
  : list (positive * list positive) :=
match bd with
| nil => acc
| l0 :: bd' =>
    match res l0 with
    | Some dts0 =>
        compute_sdom_chains_aux res bd' ((l0, (rev (l0 :: dts0)))::acc)
    | None => compute_sdom_chains_aux res bd' acc
    end
end.

Definition compute_sdom_chains (res: positive -> LDoms.t) rd
  : list (positive * list positive) :=
compute_sdom_chains_aux res rd nil.

Definition create_dtree_from_chain dt chain : DTree :=
match chain with
| p::((ch::_) as chain') => dtree_insert dt p ch chain'
| _ => dt
end.

Definition create_dtree (pe:positive) (rd:list positive) 
  (res: positive -> LDoms.t) : DTree :=
let chains := compute_sdom_chains res rd in
fold_left 
  (fun acc elt => let '(_, chain):=elt in create_dtree_from_chain acc chain)
  chains (DT_node pe DT_nil).
