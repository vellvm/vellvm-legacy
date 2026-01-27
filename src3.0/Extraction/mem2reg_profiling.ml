open Coqlib
open Datatypes
open Iteration
open List0
open Maps
open MetatheoryAtom
open Alist
open Analysis
open Infrastructure
open Mem2reg
open Pass_combinators
open Primitives
open Syntax

let num_of_las = ref 0
let num_of_sas = ref 0
let num_of_laa = ref 0
let num_of_redundant_phi = ref 0
let num_of_pruned_phi = ref 0

(** val map_filter :
    ('a1 -> bool) -> ('a1 -> 'a1) -> 'a1 list -> 'a1 list **)

let rec map_filter cond f = function
  | [] -> []
  | x::l0 ->
      if cond x then (f x)::(map_filter cond f l0) else map_filter cond f l0

(** val subst_remove_block :
    LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.block -> LLVMsyntax.block **)

let subst_remove_block id' v' = function
  | LLVMsyntax.Coq_block_intro (l0, ps0, cs0, tmn0) ->
      LLVMsyntax.Coq_block_intro (l0,
      (map_filter (fun p ->
        negb (proj_sumbool (LLVMinfra.id_dec (LLVMinfra.getPhiNodeID p) id')))
        (subst_phi id' v') ps0),
      (map_filter (fun c ->
        negb (proj_sumbool (LLVMinfra.id_dec (LLVMinfra.getCmdLoc c) id')))
        (subst_cmd id' v') cs0), (subst_tmn id' v' tmn0))

(** val subst_remove_fdef :
    LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.fdef -> LLVMsyntax.fdef **)

let subst_remove_fdef id' v' = function
  | LLVMsyntax.Coq_fdef_intro (fh, bs) -> LLVMsyntax.Coq_fdef_intro (fh,
      (map (subst_remove_block id' v') bs))

type stld_state =
  | STLD_init
  | STLD_store of LLVMsyntax.id * LLVMsyntax.value
  | STLD_alloca of LLVMsyntax.typ

(** val stld_state_rect :
    'a1 -> (LLVMsyntax.id -> LLVMsyntax.value -> 'a1) -> (LLVMsyntax.typ ->
    'a1) -> stld_state -> 'a1 **)

let stld_state_rect f f0 f1 = function
  | STLD_init -> f
  | STLD_store (x, x0) -> f0 x x0
  | STLD_alloca x -> f1 x

(** val stld_state_rec :
    'a1 -> (LLVMsyntax.id -> LLVMsyntax.value -> 'a1) -> (LLVMsyntax.typ ->
    'a1) -> stld_state -> 'a1 **)

let stld_state_rec f f0 f1 = function
  | STLD_init -> f
  | STLD_store (x, x0) -> f0 x x0
  | STLD_alloca x -> f1 x

type action =
  | AC_remove
  | AC_vsubst of LLVMsyntax.value
  | AC_tsubst of LLVMsyntax.typ

(** val action_rect :
    'a1 -> (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.typ -> 'a1) -> action ->
    'a1 **)

let action_rect f f0 f1 = function
  | AC_remove -> f
  | AC_vsubst x -> f0 x
  | AC_tsubst x -> f1 x

(** val action_rec :
    'a1 -> (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.typ -> 'a1) -> action ->
    'a1 **)

let action_rec f f0 f1 = function
  | AC_remove -> f
  | AC_vsubst x -> f0 x
  | AC_tsubst x -> f1 x

(** val subst_actions :
    LLVMsyntax.id -> LLVMsyntax.value -> action coq_AssocList -> action
    coq_AssocList **)

let subst_actions id0 v0 pairs =
  map (fun elt ->
    let id1,y = elt in
    (match y with
       | AC_vsubst v1 -> id1,(AC_vsubst (subst_value id0 v0 v1))
       | _ -> elt)) pairs

(** val substs_actions : action coq_AssocList -> action coq_AssocList **)

let rec substs_actions = function
  | [] -> []
  | elt::pairs' ->
      let id1,a = elt in
      (match a with
         | AC_remove -> elt::(substs_actions pairs')
         | AC_vsubst v1 -> (id1,(AC_vsubst
             v1))::(subst_actions id1 v1 (substs_actions pairs'))
         | AC_tsubst t1 -> (id1,(AC_tsubst
             t1))::(subst_actions id1 (LLVMsyntax.Coq_value_const
                     (LLVMsyntax.Coq_const_undef t1))
                     (substs_actions pairs')))

(** val apply_action :
    LLVMsyntax.fdef -> (LLVMsyntax.id*action) -> LLVMsyntax.fdef **)

let apply_action f = function
  | id1,ac1 ->
      (match ac1 with
         | AC_remove -> remove_fdef id1 f
         | AC_vsubst v1 -> subst_remove_fdef id1 v1 f
         | AC_tsubst t1 ->
             subst_remove_fdef id1 (LLVMsyntax.Coq_value_const
               (LLVMsyntax.Coq_const_undef t1)) f)

(** val apply_actions :
    LLVMsyntax.fdef -> action coq_AssocList -> LLVMsyntax.fdef **)

let apply_actions f pairs =
  fold_left apply_action (substs_actions pairs) f

(** val find_stld_pair_cmd :
    LLVMsyntax.id -> (stld_state*action coq_AssocList) -> LLVMsyntax.cmd ->
    stld_state*action coq_AssocList **)

let find_stld_pair_cmd pid acc c =
  let st,actions = acc in
  (match c with
     | LLVMsyntax.Coq_insn_alloca (qid, ty, value5, align5) ->
         if LLVMinfra.id_dec pid qid then (STLD_alloca ty),actions else acc
     | LLVMsyntax.Coq_insn_load (lid, typ5, value1, align5) ->
         (match value1 with
            | LLVMsyntax.Coq_value_id qid ->
                if LLVMinfra.id_dec pid qid
                then (match st with
                        | STLD_init -> acc
                        | STLD_store (i, v') -> 
                            (incr num_of_las;
                            st,((lid,(AC_vsubst v'))::actions))
                        | STLD_alloca ty' -> 
                            (incr num_of_laa;
                            st,((lid,(AC_tsubst ty'))::actions)))
                else acc
            | LLVMsyntax.Coq_value_const const5 -> acc)
     | LLVMsyntax.Coq_insn_store (sid, typ5, v0, value2, align5) ->
         (match value2 with
            | LLVMsyntax.Coq_value_id qid ->
                if LLVMinfra.id_dec pid qid
                then (match st with
                        | STLD_store (sid', v) -> 
                            (incr num_of_sas;
                            (STLD_store (sid, v0)),((sid',AC_remove)::actions))
                        | _ -> (STLD_store (sid, v0)),actions)
                else acc
            | LLVMsyntax.Coq_value_const const5 -> acc)
     | _ -> acc)

(** val find_stld_pairs_cmds :
    LLVMsyntax.cmds -> LLVMsyntax.id -> action coq_AssocList **)

let find_stld_pairs_cmds cs pid =
  snd (fold_left (find_stld_pair_cmd pid) cs (STLD_init,[]))

(** val find_stld_pairs_block :
    LLVMsyntax.id -> LLVMsyntax.block -> action coq_AssocList **)

let find_stld_pairs_block pid = function
  | LLVMsyntax.Coq_block_intro (l5, phinodes5, cs, terminator5) ->
      find_stld_pairs_cmds cs pid

(** val elim_stld_fdef :
    LLVMsyntax.id -> LLVMsyntax.fdef -> LLVMsyntax.fdef **)

let elim_stld_fdef pid f = match f with
  | LLVMsyntax.Coq_fdef_intro (fheader5, bs) ->
      let pairs = flat_map id (map (find_stld_pairs_block pid) bs) in
      apply_actions f pairs

(** val find_stld_pair_cmd' :
    LLVMsyntax.id -> (stld_state*(action coq_AssocList*LLVMsyntax.cmds)) ->
    LLVMsyntax.cmd -> stld_state*(action coq_AssocList*LLVMsyntax.cmds) **)

let find_stld_pair_cmd' pid acc c =
  let st,p = acc in
  let actions,cs = p in
  (match c with
     | LLVMsyntax.Coq_insn_alloca (qid, ty, value5, align5) ->
         if LLVMinfra.id_dec pid qid
         then (STLD_alloca ty),(actions,(c::cs))
         else st,(actions,(c::cs))
     | LLVMsyntax.Coq_insn_load (lid, typ5, value1, align5) ->
         (match value1 with
            | LLVMsyntax.Coq_value_id qid ->
                if LLVMinfra.id_dec pid qid
                then (match st with
                        | STLD_init -> st,(actions,(c::cs))
                        | STLD_store (i, v') -> st,(((lid,(AC_vsubst
                            v'))::actions),(c::cs))
                        | STLD_alloca ty' -> st,(((lid,(AC_tsubst
                            ty'))::actions),(c::cs)))
                else st,(actions,(c::cs))
            | LLVMsyntax.Coq_value_const const5 -> st,(actions,(c::cs)))
     | LLVMsyntax.Coq_insn_store (sid, typ5, v0, value2, align5) ->
         (match value2 with
            | LLVMsyntax.Coq_value_id qid ->
                if LLVMinfra.id_dec pid qid
                then (match st with
                        | STLD_store (sid', v) -> (STLD_store (sid,
                            v0)),(actions,cs)
                        | _ -> (STLD_store (sid, v0)),(actions,(c::cs)))
                else st,(actions,(c::cs))
            | LLVMsyntax.Coq_value_const const5 -> st,(actions,(c::cs)))
     | _ -> st,(actions,(c::cs)))

(** val find_stld_pairs_cmds' :
    LLVMsyntax.cmds -> action coq_AssocList -> LLVMsyntax.id -> action
    coq_AssocList*LLVMsyntax.cmds **)

let find_stld_pairs_cmds' cs actions pid =
  snd (fold_left (find_stld_pair_cmd' pid) cs (STLD_init,(actions,[])))

(** val find_stld_pairs_block' :
    LLVMsyntax.id -> (action coq_AssocList*LLVMsyntax.blocks) ->
    LLVMsyntax.block -> action coq_AssocList*LLVMsyntax.blocks **)

let find_stld_pairs_block' pid acc b =
  let actions,bs = acc in
  let LLVMsyntax.Coq_block_intro (l5, phinodes5, cs, terminator5) = b in
  let actions',cs' = find_stld_pairs_cmds' cs actions pid in
  actions',((LLVMsyntax.Coq_block_intro (l5, phinodes5, 
  (rev cs'), terminator5))::bs)

(** val elim_stld_fdef' :
    LLVMsyntax.id -> LLVMsyntax.fdef -> LLVMsyntax.fdef **)

let elim_stld_fdef' pid = function
  | LLVMsyntax.Coq_fdef_intro (fh, bs) ->
      let pairs,bs' = fold_left (find_stld_pairs_block' pid) bs ([],[]) in
      apply_actions (LLVMsyntax.Coq_fdef_intro (fh, (rev bs'))) pairs

(** val macro_mem2reg_fdef_iter :
    LLVMsyntax.fdef -> LLVMsyntax.l list -> LLVMsyntax.l list ATree.t ->
    LLVMsyntax.l list ATree.t -> LLVMsyntax.id list ->
    (LLVMsyntax.fdef*bool)*LLVMsyntax.id list **)

let macro_mem2reg_fdef_iter f rd succs preds dones =
  match LLVMinfra.getEntryBlock f with
    | Some b ->
        let LLVMsyntax.Coq_block_intro (l5, phinodes5, cs, terminator5) = b
        in
        (match find_promotable_alloca f cs dones with
           | Some p ->
               let p0,al = p in
               let p1,num = p0 in
               let pid,ty = p1 in
               ((seq_trans (phinodes_placement rd pid ty al succs preds)
                  (seq_trans
                    (cond_trans (fun x -> does_stld_elim ())
                      (elim_stld_fdef pid) id)
                    (seq_trans
                      (cond_trans (load_in_fdef pid) id
                        (elim_dead_st_fdef pid))
                      (cond_trans (used_in_fdef pid) id (remove_fdef pid))))
                  f),true),(pid::dones)
           | None -> (f,false),dones)
    | None -> (f,false),dones

(** val macro_mem2reg_fdef_step :
    LLVMsyntax.l list -> LLVMsyntax.l list ATree.t -> LLVMsyntax.l list
    ATree.t -> (LLVMsyntax.fdef*LLVMsyntax.id list) ->
    (LLVMsyntax.fdef*LLVMsyntax.id list, LLVMsyntax.fdef*LLVMsyntax.id list)
    sum **)

let macro_mem2reg_fdef_step rd succs preds = function
  | f,dones ->
      let p,dones1 = macro_mem2reg_fdef_iter f rd succs preds dones in
      let f1,changed1 = p in
      if changed1 then Coq_inr (f1,dones1) else Coq_inl (f1,dones1)

(** val elim_phi_phi :
    LLVMsyntax.fdef -> action coq_AssocList -> LLVMsyntax.phinode -> action
    coq_AssocList **)

let elim_phi_phi f acc = function
  | LLVMsyntax.Coq_insn_phi (pid, typ5, vls) ->
      let ndpvs =
        remove_redundancy [] ((LLVMsyntax.Coq_value_id pid)::(map fst vls))
      in
      (match ndpvs with
         | [] ->
             if does_dead_phi_elim ()
             then if used_in_fdef pid f then acc 
                  else 
                    (incr num_of_pruned_phi;
                    (pid,AC_remove)::acc)
             else acc
         | v1::l0 ->
             (match v1 with
                | LLVMsyntax.Coq_value_id id1 ->
                    (match l0 with
                       | [] -> (pid,AC_remove)::acc
                       | v2::l1 ->
                           (match l1 with
                              | [] ->
                                  (incr num_of_redundant_phi;
                                  if LLVMinfra.id_dec pid id1
                                  then (pid,(AC_vsubst v2))::acc
                                  else (pid,(AC_vsubst v1))::acc)
                              | v::l2 ->
                                  if does_dead_phi_elim ()
                                  then if used_in_fdef pid f
                                       then acc
                                       else 
                                         (incr num_of_pruned_phi;
                                         (pid,AC_remove)::acc)
                                  else acc))
                | LLVMsyntax.Coq_value_const const5 ->
                    (match l0 with
                       | [] -> 
                           (incr num_of_pruned_phi;
                           (pid,AC_remove)::acc)
                       | v::l1 ->
                           (match l1 with
                              | [] -> 
                                  (incr num_of_redundant_phi;
                                   (pid,(AC_vsubst v1))::acc)
                              | v0::l2 ->
                                  if does_dead_phi_elim ()
                                  then if used_in_fdef pid f
                                       then acc
                                       else 
                                         (incr num_of_pruned_phi;
                                         (pid,AC_remove)::acc)
                                  else acc))))

(** val elim_phi_phis :
    LLVMsyntax.fdef -> LLVMsyntax.phinode list -> action coq_AssocList **)

let elim_phi_phis f ps =
  fold_left (elim_phi_phi f) ps []

(** val elim_phi_block :
    LLVMsyntax.fdef -> LLVMsyntax.block -> action coq_AssocList **)

let elim_phi_block f = function
  | LLVMsyntax.Coq_block_intro (l5, ps, cmds5, terminator5) ->
      elim_phi_phis f ps

(** val elim_phi_fdef : LLVMsyntax.fdef -> (AtomImpl.atom*action) list **)

let elim_phi_fdef f = match f with
  | LLVMsyntax.Coq_fdef_intro (fh, bs) ->
      flat_map id (map (elim_phi_block f) bs)

(** val elim_phi_step :
    LLVMsyntax.fdef -> (LLVMsyntax.fdef, LLVMsyntax.fdef) sum **)

let elim_phi_step f =
  match elim_phi_fdef f with
    | [] -> Coq_inl f
    | p::l0 -> Coq_inr (apply_actions f (p::l0))

(** val elim_phi_phi' :
    LLVMsyntax.fdef -> (action coq_AssocList*LLVMsyntax.phinodes) ->
    LLVMsyntax.phinode -> action coq_AssocList*LLVMsyntax.phinodes **)

let elim_phi_phi' f acc p =
  let actions,ps = acc in
  let LLVMsyntax.Coq_insn_phi (pid, typ5, vls) = p in
  let ndpvs =
    remove_redundancy [] ((LLVMsyntax.Coq_value_id pid)::(map fst vls))
  in
  (match ndpvs with
     | [] ->
         if does_dead_phi_elim ()
         then if used_in_fdef pid f then actions,(p::ps) else actions,ps
         else actions,(p::ps)
     | v1::l0 ->
         (match v1 with
            | LLVMsyntax.Coq_value_id id1 ->
                (match l0 with
                   | [] -> actions,ps
                   | v2::l1 ->
                       (match l1 with
                          | [] ->
                              if LLVMinfra.id_dec pid id1
                              then ((pid,(AC_vsubst v2))::actions),(p::ps)
                              else ((pid,(AC_vsubst v1))::actions),(p::ps)
                          | v::l2 ->
                              if does_dead_phi_elim ()
                              then if used_in_fdef pid f
                                   then actions,(p::ps)
                                   else actions,ps
                              else actions,(p::ps)))
            | LLVMsyntax.Coq_value_const const5 ->
                (match l0 with
                   | [] -> actions,ps
                   | v::l1 ->
                       (match l1 with
                          | [] -> ((pid,(AC_vsubst v1))::actions),(p::ps)
                          | v0::l2 ->
                              if does_dead_phi_elim ()
                              then if used_in_fdef pid f
                                   then actions,(p::ps)
                                   else actions,ps
                              else actions,(p::ps)))))

(** val elim_phi_phis' :
    LLVMsyntax.fdef -> action coq_AssocList -> LLVMsyntax.phinode list ->
    action coq_AssocList*LLVMsyntax.phinodes **)

let elim_phi_phis' f actions ps =
  fold_left (elim_phi_phi' f) ps (actions,[])

(** val elim_phi_block' :
    LLVMsyntax.fdef -> (action coq_AssocList*LLVMsyntax.block list) ->
    LLVMsyntax.block -> action coq_AssocList*LLVMsyntax.block list **)

let elim_phi_block' f acc b =
  let actions,bs = acc in
  let LLVMsyntax.Coq_block_intro (l5, ps, cmds5, terminator5) = b in
  let actions',ps' = elim_phi_phis' f actions ps in
  actions',((LLVMsyntax.Coq_block_intro (l5, (rev ps'), cmds5,
  terminator5))::bs)

(** val elim_phi_fdef' :
    LLVMsyntax.fdef -> action coq_AssocList*LLVMsyntax.fdef **)

let elim_phi_fdef' f = match f with
  | LLVMsyntax.Coq_fdef_intro (fh, bs) ->
      let actions,bs' = fold_left (elim_phi_block' f) bs ([],[]) in
      actions,(LLVMsyntax.Coq_fdef_intro (fh, (rev bs')))

(** val elim_phi_step' :
    LLVMsyntax.fdef -> (LLVMsyntax.fdef, LLVMsyntax.fdef) sum **)

let elim_phi_step' f =
  let actions,f' = elim_phi_fdef' f in
  (match actions with
     | [] -> Coq_inl f'
     | p::l0 -> Coq_inr (apply_actions f' actions))

(** val mem2reg_fdef : LLVMsyntax.fdef -> LLVMsyntax.fdef **)

let mem2reg_fdef f =
  match LLVMinfra.getEntryBlock f with
    | Some b ->
        (match reachablity_analysis f with
           | Some rd ->
               if print_reachablity rd
               then let f1,l0 =
                      let succs = Cfg.successors f in
                      let preds = XATree.make_predecessors succs in
                      SafePrimIter.iterate
                        (macro_mem2reg_fdef_step rd succs preds) (f,[])
                    in
                    if does_phi_elim ()
                    then SafePrimIter.iterate elim_phi_step f1
                    else f1
               else f
           | None -> f)
    | None -> f

(** val run : LLVMsyntax.coq_module -> LLVMsyntax.coq_module **)

let run = function
  | LLVMsyntax.Coq_module_intro (los, nts, ps) -> 
      let m = LLVMsyntax.Coq_module_intro
               (los, nts,
                (map (fun p ->
                      match p with
                      | LLVMsyntax.Coq_product_fdef f -> 
                          LLVMsyntax.Coq_product_fdef (mem2reg_fdef f)
                      | _ -> p) ps)) in
      Printf.printf "las:%d, laa:%d, sas:%d; redundant:%d, pruned:%d\n" 
        !num_of_las !num_of_laa !num_of_sas !num_of_redundant_phi !num_of_pruned_phi;
      m

(*************************************************)
(* The following is the Coq code that 
   generates elim_stld_fdef' and elim_phi_step'. *)

(* Definition find_stld_pair_cmd' (pid:id)  *)
(*   (acc:stld_state * (AssocList action * cmds))  *)
(*   (c:cmd) : stld_state * (AssocList action * cmds) := *)
(* let '(st, (actions, cs)) := acc in *)
(* match c with *)
(* | insn_alloca qid ty value5 align5 => *)
(*     if id_dec pid qid *)
(*     then (STLD_alloca ty, (actions, c::cs)) *)
(*     else (st, (actions, c::cs)) *)
(* | insn_store sid typ5 v0 value2 align5 => *)
(*     match value2 with *)
(*     | value_id qid => *)
(*        if id_dec pid qid *)
(*        then  *)
(*          match st with *)
(*          | STLD_store sid' _ =>  *)
(*              (STLD_store sid v0, (actions, cs)) *)
(*          | _ => (STLD_store sid v0, (actions, c::cs)) *)
(*          end *)
(*       else (st, (actions, c::cs)) *)
(*     | value_const const5 => (st, (actions, c::cs)) *)
(*     end *)
(* | insn_load lid typ5 value1 align5 => *)
(*     match value1 with *)
(*     | value_id qid => *)
(*        if id_dec pid qid *)
(*        then  *)
(*          match st with *)
(*          | STLD_store _ v' => (st, ((lid, AC_vsubst v')::actions, c::cs)) *)
(*          | STLD_alloca ty' => (st, ((lid, AC_tsubst ty')::actions, c::cs)) *)
(*          | _ => (st, (actions, c::cs)) *)
(*          end *)
(*        else (st, (actions, c::cs)) *)
(*     | value_const const5 => (st, (actions, c::cs)) *)
(*     end *)
(* | _ => (st, (actions, c::cs)) *)
(* end. *)

(* Definition find_stld_pairs_cmds' (cs:cmds) (actions: AssocList action) (pid:id)  *)
(*   : AssocList action * cmds := *)
(* snd (List.fold_left (find_stld_pair_cmd' pid) cs (STLD_init, (actions, nil))). *)

(* Definition find_stld_pairs_block' (pid:id) (acc: AssocList action * blocks)  *)
(*   (b : block) : AssocList action * blocks := *)
(* let '(actions, bs) := acc in *)
(* let '(block_intro l5 phinodes5 cs terminator5) := b in *)
(* let '(actions', cs') := find_stld_pairs_cmds' cs actions pid in *)
(* (actions', block_intro l5 phinodes5 (List.rev cs') terminator5 :: bs). *)

(* Definition elim_stld_fdef' (pid:id) (f:fdef) : fdef := *)
(* let '(fdef_intro fh bs) := f in *)
(* let '(pairs, bs') := fold_left (find_stld_pairs_block' pid) bs (nil,nil) in *)
(* apply_actions (fdef_intro fh (List.rev bs')) pairs. *)

(* Definition elim_phi_phi' (f:fdef) (acc : AssocList action * phinodes) (p:phinode) *)
(*   : AssocList action * phinodes := *)
(* let '(actions, ps) := acc in *)
(* let '(insn_phi pid _ vls) := p in  *)
(* let ndpvs :=  *)
(*   remove_redundancy nil (value_id pid::List.map fst vls)  *)
(* in *)
(* match ndpvs with *)
(* | value_id id1 as v1::v2::nil => *)
(*     if (id_dec pid id1) then  *)
(*       (\* if v1 is pid, then v2 cannot be pid*\) *)
(*       ((pid, AC_vsubst v2)::actions, p::ps) *)
(*     else   *)
(*       (\* if v1 isnt pid, then v2 must be pid*\) *)
(*       ((pid, AC_vsubst v1)::actions, p::ps) *)
(* | value_const _ as v1::_::nil => *)
(*     (\* if v1 is const, then v2 must be pid*\) *)
(*     ((pid, AC_vsubst v1)::actions, p::ps) *)
(* | v1::nil =>  *)
(*     (\* v1 must be pid, so pn:= pid = phi [pid, ..., pid] *\) *)
(*     (actions, ps) *)
(* | _ =>  *)
(*    if does_dead_phi_elim tt then *)
(*       if used_in_fdef pid f then (actions, p::ps) else (actions, ps) *)
(*    else (actions, p::ps) *)
(* end. *)

(* Definition elim_phi_phis' f actions ps : AssocList action * phinodes := *)
(* List.fold_left (elim_phi_phi' f) ps (actions, nil). *)

(* Definition elim_phi_block' f acc b := *)
(* let '(actions, bs) := acc in  *)
(* let '(block_intro l5 ps cmds5 terminator5) := b in *)
(* let '(actions', ps') := elim_phi_phis' f actions ps in  *)
(* (actions', block_intro l5 (List.rev ps') cmds5 terminator5 :: bs). *)

(* Definition elim_phi_fdef' f := *)
(* let '(fdef_intro fh bs) := f in *)
(* let '(actions, bs') := List.fold_left (elim_phi_block' f) bs (nil, nil) in *)
(* (actions, fdef_intro fh (List.rev bs')). *)

(* Definition elim_phi_step' f := *)
(* let '(actions, f') := elim_phi_fdef' f in *)
(* match actions with *)
(* | nil => inl f' *)
(* | pairs => inr (apply_actions f' pairs) *)
(* end. *)

