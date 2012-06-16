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

Definition apply_action (f:fdef) (elt:id * action): fdef :=
let '(id1, ac1) := elt in
match ac1 with
| AC_vsubst v1 => remove_fdef id1 (subst_fdef id1 v1 f)
| AC_tsubst t1 => 
    remove_fdef id1 (subst_fdef id1 (value_const (const_undef t1)) f)
| AC_remove => remove_fdef id1 f
end.

Definition action2value (ac:action) : option value :=
match ac with
| AC_vsubst v1 => Some v1
| AC_tsubst t1 => Some (value_const (const_undef t1))
| _ => None
end.

Definition subst_action (id0:id) (v0:value) (ac:action): action :=
match ac with
| AC_vsubst v1 => AC_vsubst (subst_value id0 v0 v1)
| _ => ac
end.

(************************************************)

Module Type XMap.

Variable t : Type -> Type.

Parameter empty : forall (A:Type), t A.
Parameter add : forall (A:Type), id -> A -> t A -> t A.
Parameter find : forall (A:Type), id -> t A -> option A.
Parameter map : forall A B : Type, (A -> B) -> t A -> t B.
Parameter fold : forall A B : Type, (B -> (id * A) -> B) -> t A -> B -> B.

Implicit Arguments empty [A].
Implicit Arguments add [A].
Implicit Arguments find [A].
Implicit Arguments map [A B].
Implicit Arguments fold [A B].

End XMap. 

Module AtomOT <: OrderedType with Definition t := id.

  Definition t := id.

  Definition eq := @eq t.
  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_eq t.
  Definition eq_trans := @trans_eq t.

  Definition eq_dec := eq_atom_dec.

  Parameter lt : t -> t -> Prop.
  
  Axiom lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Axiom lt_not_eq : forall x y : t, lt x y -> ~ eq x y.

  Parameter compare : forall x y : t, Compare lt eq x y.

End AtomOT.

Require Import FMapAVL.

Module AVLMap <: XMap. 

Module AtomFMapAVL := FMapAVL.Make (AtomOT).

Definition t := AtomFMapAVL.t.

Definition empty (A:Type) : t A := AtomFMapAVL.empty A.
Definition add := AtomFMapAVL.add.
Definition find := AtomFMapAVL.find.
Definition map (A B : Type) (f: A -> B) (mp: t A) : t B :=
  AtomFMapAVL.map f mp.
Definition fold (A B : Type) (f: B -> (id * A) -> B) (mp:t A) (init: B) : B :=
  AtomFMapAVL.fold (fun k v acc => f acc (k, v)) mp init.

Implicit Arguments empty [A].
Implicit Arguments map [A B].
Implicit Arguments fold [A B].

End AVLMap.

Module ListMap <: XMap.

Definition t := AssocList.

Definition empty (A:Type) : t A := nil.
Definition add (A:Type) (key:id) (e:A) (mp:t A) : t A := (key,e)::mp.
Definition find (A:Type) (key:id) (mp:t A) : option A := lookupAL _ mp key.
Definition map (A B : Type) (f: A -> B) (mp: t A) : t B := 
  List.map (fun elt => let '(id0, a0) := elt in (id0, f a0)) mp.
Definition fold (A B : Type) (f: B -> (id * A) -> B) (mp:t A) (init: B) : B :=
  List.fold_left f mp init.

Implicit Arguments empty [A].
Implicit Arguments add [A].
Implicit Arguments find [A].
Implicit Arguments map [A B].
Implicit Arguments fold [A B].

End ListMap.

Module ComposedPass (M:XMap).

Definition substs_value (mp:M.t action) (v:value) : value :=
match v with
| value_id id1 => 
    match M.find id1 mp with
    | Some ac1 => 
       match action2value ac1 with
       | Some v1 => v1
       | _ => v
       end
    | _ => v
    end
| _ => v
end.

Notation "v {[ mp ]}" :=
  ( substs_value mp v ) (at level 42, no associativity).

Fixpoint substs_list_value (mp:M.t action) (vl:list (sz * value))
  : list (sz * value) :=
match vl with
| nil => nil
| (sz0, v0) :: tl =>
  (sz0, (v0 {[mp]})) :: (substs_list_value mp tl)
end.

Definition substs_cmd (mp:M.t action) (c:cmd) : cmd :=
match c with
| insn_bop id0 t0 bop0 v1 v2 =>
    insn_bop id0 t0 bop0 (v1{[mp]}) (v2{[mp]})
| insn_fbop id0 fbop0 fp0 v1 v2 =>
    insn_fbop id0 fbop0 fp0 (v1{[mp]}) (v2{[mp]})
| insn_extractvalue id0 t v cnts t' =>
    insn_extractvalue id0 t (v{[mp]}) cnts t'
| insn_insertvalue id0 t1 v1 t2 v2 cnts =>
    insn_insertvalue id0 t1 (v1{[mp]}) t2 (v2{[mp]}) cnts
| insn_malloc id0 t v al => insn_malloc id0 t (v{[mp]}) al
| insn_free id0 t v => insn_free id0 t (v{[mp]})
| insn_alloca id0 t v al => insn_alloca id0 t (v{[mp]}) al
| insn_load id0 t v al => insn_load id0 t (v{[mp]}) al
| insn_store id0 t1 v1 v2 al =>
    insn_store id0 t1 (v1{[mp]}) (v2{[mp]}) al
| insn_gep id0 ib0 t v vs t' =>
    insn_gep id0 ib0 t (v{[mp]}) (substs_list_value mp vs) t'
| insn_trunc id0 top0 t1 v1 t2 => insn_trunc id0 top0 t1 (v1{[mp]}) t2
| insn_ext id0 eop0 t1 v1 t2 => insn_ext id0 eop0 t1 (v1{[mp]}) t2
| insn_cast id0 cop0 t1 v1 t2 => insn_cast id0 cop0 t1 (v1{[mp]}) t2
| insn_icmp id0 t0 cond0 v1 v2 =>
    insn_icmp id0 t0 cond0 (v1{[mp]}) (v2{[mp]})
| insn_fcmp id0 fcond0 fp0 v1 v2 =>
    insn_fcmp id0 fcond0 fp0 (v1{[mp]}) (v2{[mp]})
| insn_select id0 v0 t0 v1 v2 =>
    insn_select id0 (v0{[mp]}) t0 (v1{[mp]}) (v2{[mp]})
| insn_call id0 noret0 cl0 rt1 va1 v1 ps =>
    insn_call id0 noret0 cl0 rt1 va1 (v1{[mp]})
      (List.map (fun p => let '(t, v):=p in (t, v{[mp]})) ps)
end.

Definition substs_tmn (mp:M.t action) (tmn:terminator) : terminator :=
match tmn with
| insn_br id0 v0 l1 l2 => insn_br id0 (v0{[mp]}) l1 l2
| insn_return id0 t0 v0 => insn_return id0 t0 (v0{[mp]})
| _ => tmn
end.

Fixpoint substs_list_value_l (mp:M.t action) (l0:list (value * l))
  : list (value * l) :=
match l0 with
| nil => nil
| (v0, l0) :: tl =>
  ((v0{[mp]}), l0) :: (substs_list_value_l mp tl)
end.

Definition substs_phi (mp:M.t action) (pn:phinode) : phinode :=
match pn with
| insn_phi id0 t0 vls => insn_phi id0 t0 (substs_list_value_l mp vls)
end.

Definition substs_block (mp:M.t action) (b:block) : block :=
match b with
| block_intro l0 ps0 cs0 tmn0 =>
  block_intro l0 (List.map (substs_phi mp) ps0)
    (List.map (substs_cmd mp) cs0) (substs_tmn mp tmn0)
end.

Definition substs_fdef (mp:M.t action) (f:fdef) : fdef :=
match f with
| fdef_intro fh bs => fdef_intro fh (List.map (substs_block mp) bs)
end.

Definition filters_phinode (mp:M.t action) :=
fun p => match M.find (getPhiNodeID p) mp with
         | Some _ => false
         | None => true
         end.

Definition removes_phinodes (mp:M.t action) (ps:phinodes) : phinodes :=
  List.filter (filters_phinode mp) ps.

Definition filters_cmd (mp:M.t action) :=
fun c => match M.find (getCmdLoc c) mp with
         | Some _ => false
         | None => true
         end.

Definition removes_cmds (mp:M.t action) (cs:cmds) : cmds :=
  List.filter (filters_cmd mp) cs.

Definition removes_block (mp:M.t action) (b:block) : block :=
match b with
| block_intro l0 ps0 cs0 tmn0 =>
  block_intro l0 (removes_phinodes mp ps0) (removes_cmds mp cs0) tmn0
end.

Definition removes_fdef (mp:M.t action) (f:fdef) : fdef :=
match f with
| fdef_intro fh bs => fdef_intro fh (List.map (removes_block mp) bs)
end.

Definition substs_removes_block (mp:M.t action) b :=
let '(block_intro l0 ps0 cs0 tmn0) := b in
block_intro l0
  (map_filter (filters_phinode mp) (substs_phi mp) ps0)
  (map_filter (filters_cmd mp) (substs_cmd mp) cs0) 
  (substs_tmn mp tmn0).

Definition substs_removes_fdef (mp:M.t action) f :=
let '(fdef_intro fh bs) := f in
fdef_intro fh (List.map (substs_removes_block mp) bs).

(* If subst_actions calls subst_action directly, but not the unfolded 
   version, the extractable will have a heisenbug. *)
Definition subst_actions (id0:id) (ac0:action) (pairs: M.t action) :
  M.t action :=
match action2value ac0 with
| None => pairs 
| Some v0 => 
    M.map (fun ac => 
           match ac with
           | AC_vsubst v1 => AC_vsubst (subst_value id0 v0 v1)
           | _ => ac
           end) pairs
end.

Definition find_parent_action (ac1:action) (mac: M.t action) : action :=
match ac1 with 
| AC_vsubst (value_id id1) =>
    match M.find id1 mac with
    | Some ac1' => 
        match ac1' with
        | AC_remove => ac1
        | _ => ac1'
        end
    | _ => ac1
    end
| _ => ac1
end.

Fixpoint compose_actions (pairs: AssocList action) : M.t action :=
match pairs with 
| nil => M.empty
| (id1, ac2)::pairs' => 
  let acc := compose_actions pairs' in 
  let ac2' := find_parent_action ac2 acc in
  M.add id1 ac2' (subst_actions id1 ac2' acc)
end.

Definition run (pairs: AssocList action) (f:fdef) : fdef :=
let mp := compose_actions pairs in
substs_removes_fdef mp f.

Lemma filters_phinode__substs_phi: forall actions p,
  filters_phinode actions p = filters_phinode actions (substs_phi actions p).
Proof.
  destruct p; unfold filters_phinode; simpl; auto.
Qed.

Lemma substs_removes_phinodes__commute: 
  forall actions ps,
  map_filter (filters_phinode actions) (substs_phi actions) ps =
    removes_phinodes actions (List.map (substs_phi actions) ps).
Proof.
  induction ps as [|p ps]; simpl; auto.
    rewrite IHps. rewrite filters_phinode__substs_phi; auto.
Qed.

Lemma filters_cmd__substs_cmd: forall actions c,
  filters_cmd actions c = filters_cmd actions (substs_cmd actions c).
Proof.
  destruct c; unfold filters_cmd; simpl; auto.
Qed.

Lemma substs_removes_cmds__commute: forall actions cs,
  map_filter (filters_cmd actions) (substs_cmd actions) cs =
    removes_cmds actions (List.map (substs_cmd actions) cs).
Proof.
  induction cs as [|c cs]; simpl; auto.
    rewrite IHcs. rewrite filters_cmd__substs_cmd; auto.
Qed.

Lemma substs_removes_fdef__commute: forall actions f1,
  substs_removes_fdef actions f1 = removes_fdef actions (substs_fdef actions f1).
Proof.
  destruct f1 as [fh1 bs1]. simpl.
  f_equal.
  induction bs1 as [|[l1 ps1 cs1 tmn1] bs1]; simpl; auto.
    f_equal; auto.
    f_equal; auto.
      apply substs_removes_phinodes__commute.
      apply substs_removes_cmds__commute.
    Qed.

Lemma find_parent_action_inv: forall ac1 mac ac2 
  (Hfind: find_parent_action ac1 mac = ac2),
  ac1 = ac2 \/ 
  exists id1, 
    ac1 = AC_vsubst (value_id id1) /\ M.find id1 mac = Some ac2 /\ 
    ac2 <> AC_remove.
Proof.
  intros. subst.
  destruct ac1; auto.
  destruct v; auto.
  simpl.
  case_eq (M.find id5 mac); eauto.
  intros [] Hfind; try solve 
    [auto | right; exists id5; repeat split; auto; congruence].
Qed.

Fixpoint substs_actions (pairs: AssocList action) : M.t action :=
match pairs with 
| nil => M.empty
| (id1, ac1)::pairs' => 
    M.add id1 ac1 (subst_actions id1 ac1 (substs_actions pairs'))
end.

Definition pipelined_actions (pairs: AssocList action) (f:fdef) : fdef :=
M.fold apply_action (substs_actions pairs) f.

End ComposedPass.

Module AVLComposedPass := ComposedPass (AVLMap).
Module ListComposedPass := ComposedPass (ListMap).

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
AVLComposedPass.run pairs f.

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



