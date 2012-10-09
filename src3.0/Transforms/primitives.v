Require Import vellvm.
Require Import Lattice.
Require Import Maps.
Require Import dom_tree.
Require Import trans_tactic.

(* This file defines primitives to implement transformations. *)

(**************************************************************)
(* transformers                                               *)
Definition trans_block (trans_stmts: stmts -> stmts) (b:block) : block :=
match b with
| (l0, sts0) => (l0, trans_stmts sts0)
end.

Definition transf_from_module (transf:fdef -> fdef) (m:module) :=
let '(module_intro los nts ps) := m in
module_intro los nts
  (List.map (fun p =>
             match p with
             | product_fdef f => product_fdef (transf f)
             | _ => p
             end) ps).

(**************************************************************)
(* substitution                                               *)
Definition subst_value (id':id) (v':value) (v:value) : value :=
match v with
| value_id id1 => if id_dec id1 id' then v' else v
| _ => v
end.

Notation "v {[ v' // id' ]}" :=
  ( subst_value id' v' v ) (at level 42, no associativity).

Fixpoint subst_list_value (id':id) (v':value) (vl:list (sz * value))
  : list (sz * value) :=
match vl with
| nil => nil
| (sz0, v0) :: tl =>
  (sz0, (v0{[v'//id']})) :: (subst_list_value id' v' tl)
end.

Definition subst_cmd (id':id) (v':value) (c:cmd) : cmd :=
match c with
| insn_bop id0 t0 bop0 v1 v2 =>
    insn_bop id0 t0 bop0 (v1{[v'//id']}) (v2{[v'//id']})
| insn_fbop id0 fbop0 fp0 v1 v2 =>
    insn_fbop id0 fbop0 fp0 (v1{[v'//id']}) (v2{[v'//id']})
| insn_extractvalue id0 t v cnts t' =>
    insn_extractvalue id0 t (v{[v'//id']}) cnts t'
| insn_insertvalue id0 t1 v1 t2 v2 cnts =>
    insn_insertvalue id0 t1 (v1{[v'//id']}) t2 (v2{[v'//id']}) cnts
| insn_malloc id0 t v al => insn_malloc id0 t (v{[v'//id']}) al
| insn_free id0 t v => insn_free id0 t (v{[v'//id']})
| insn_alloca id0 t v al => insn_alloca id0 t (v{[v'//id']}) al
| insn_load id0 t v al => insn_load id0 t (v{[v'//id']}) al
| insn_store id0 t1 v1 v2 al =>
    insn_store id0 t1 (v1{[v'//id']}) (v2{[v'//id']}) al
| insn_gep id0 ib0 t v vs t' =>
    insn_gep id0 ib0 t (v{[v'//id']}) (subst_list_value id' v' vs) t'
| insn_trunc id0 top0 t1 v1 t2 => insn_trunc id0 top0 t1 (v1{[v'//id']}) t2
| insn_ext id0 eop0 t1 v1 t2 => insn_ext id0 eop0 t1 (v1{[v'//id']}) t2
| insn_cast id0 cop0 t1 v1 t2 => insn_cast id0 cop0 t1 (v1{[v'//id']}) t2
| insn_icmp id0 t0 cond0 v1 v2 =>
    insn_icmp id0 t0 cond0 (v1{[v'//id']}) (v2{[v'//id']})
| insn_fcmp id0 fcond0 fp0 v1 v2 =>
    insn_fcmp id0 fcond0 fp0 (v1{[v'//id']}) (v2{[v'//id']})
| insn_select id0 v0 t0 v1 v2 =>
    insn_select id0 (v0{[v'//id']}) t0 (v1{[v'//id']}) (v2{[v'//id']})
| insn_call id0 noret0 cl0 rt1 va1 v1 ps =>
    insn_call id0 noret0 cl0 rt1 va1 (v1{[v'//id']})
      (List.map (fun p => let '(t, v):=p in (t, v{[v'//id']})) ps)
end.

Definition subst_tmn (id':id) (v':value) (tmn:terminator) : terminator :=
match tmn with
| insn_br id0 v0 l1 l2 => insn_br id0 (v0{[v'//id']}) l1 l2
| insn_return id0 t0 v0 => insn_return id0 t0 (v0{[v'//id']})
| _ => tmn
end.

Fixpoint subst_list_value_l (id':id) (v':value ) (l0:list (value * l))
  : list (value * l) :=
match l0 with
| nil => nil
| (v0, l0) :: tl =>
  ((v0{[v'//id']}), l0) :: (subst_list_value_l id' v' tl)
end.

Definition subst_phi (id':id) (v':value) (pn:phinode) : phinode :=
match pn with
| insn_phi id0 t0 vls => insn_phi id0 t0 (subst_list_value_l id' v' vls)
end.

Definition subst_insn (id':id) (v':value) (instr:insn) : insn :=
match instr with
| insn_phinode pn => insn_phinode (subst_phi id' v' pn)
| insn_cmd c => insn_cmd (subst_cmd id' v' c)
| insn_terminator tmn => insn_terminator (subst_tmn id' v' tmn)
end.

Definition subst_stmts (id':id) (v':value) (sts:stmts) : stmts :=
match sts with
| stmts_intro ps0 cs0 tmn0 =>
  stmts_intro (List.map (subst_phi id' v') ps0)
    (List.map (subst_cmd id' v') cs0) (subst_tmn id' v' tmn0)
end.

Definition subst_block (id':id) (v':value) (b:block) : block :=
trans_block (subst_stmts id' v') b.

Definition subst_fdef (id':id) (v':value) (f:fdef) : fdef :=
match f with
| fdef_intro fh bs => fdef_intro fh (List.map (subst_block id' v') bs)
end.

(**************************************************************)
(* substitution instance: substituting constants              *)
Definition csubst_fdef (id':id) (cst':const) : fdef -> fdef :=
subst_fdef id' (value_const cst').

Definition csubst_block (id':id) (cst':const) : block -> block :=
subst_block id' (value_const cst').

Definition csubst_phi (id':id) (cst':const) : phinode -> phinode :=
subst_phi id' (value_const cst').

Definition csubst_cmd (id':id) (cst':const) : cmd -> cmd :=
subst_cmd id' (value_const cst').

Definition csubst_tmn (id':id) (cst':const) : terminator -> terminator :=
subst_tmn id' (value_const cst').

Definition csubst_insn (id':id) (cst':const) : insn -> insn :=
subst_insn id' (value_const cst').

Definition csubst_value (id':id) (cst':const) : value -> value :=
subst_value id' (value_const cst').

(**************************************************************)
(* substitution instance: substituting variables              *)
Definition isubst_fdef (id1 id2:id) : fdef -> fdef :=
subst_fdef id1 (value_id id2).

Definition isubst_block (id1 id2:id) : block -> block :=
subst_block id1 (value_id id2).

Definition isubst_phi (id1 id2:id) : phinode -> phinode :=
subst_phi id1 (value_id id2).

Definition isubst_cmd (id1 id2:id) : cmd -> cmd :=
subst_cmd id1 (value_id id2).

Definition isubst_tmn (id1 id2:id) : terminator -> terminator :=
subst_tmn id1 (value_id id2).

Definition isubst_insn (id1 id2:id) : insn -> insn :=
subst_insn id1 (value_id id2).

Definition isubst_value (id1 id2:id) : value -> value :=
subst_value id1 (value_id id2).

Hint Unfold isubst_fdef isubst_block isubst_insn.

(**************************************************************)
(* removal                                                    *)
Definition remove_phinodes (id':id) (ps:phinodes) : phinodes :=
  (List.filter (fun p => negb (id_dec (getPhiNodeID p) id')) ps).

Definition remove_cmds (id':id) (cs:cmds) : cmds :=
  (List.filter (fun c => negb (id_dec (getCmdLoc c) id')) cs).

Definition remove_stmts (id':id) (sts:stmts) : stmts :=
match sts with
| stmts_intro ps0 cs0 tmn0 =>
  stmts_intro (remove_phinodes id' ps0) (remove_cmds id' cs0) tmn0
end.

Definition remove_block (id':id) (b:block) : block :=
trans_block (remove_stmts id') b.

Definition remove_fdef (id':id) (f:fdef) : fdef :=
match f with
| fdef_intro fh bs => fdef_intro fh (List.map (remove_block id') bs)
end.

(**************************************************************)
(* check if a variable is used                                *)
Definition used_in_value (id0:id) (v:value) : bool :=
match v with
| value_id id1 => id_dec id1 id0
| _ => false
end.

Fixpoint used_in_list_value (id0:id) (vl:list (sz * value)) : bool :=
match vl with
| nil => false
| (_, v0) :: tl =>
    used_in_value id0 v0 || used_in_list_value id0 tl
end.

Definition used_in_cmd (id':id) (c:cmd) : bool :=
match c with
| insn_bop _ _ _ v1 v2
| insn_fbop _ _ _ v1 v2
| insn_insertvalue _ _ v1 _ v2 _
| insn_store _ _ v1 v2 _
| insn_icmp _ _ _ v1 v2
| insn_fcmp _ _ _ v1 v2 =>
    used_in_value id' v1 || used_in_value id' v2
| insn_extractvalue _ _ v _ _
| insn_malloc _ _ v _
| insn_free _ _ v
| insn_alloca _ _ v _
| insn_load _ _ v _
| insn_trunc _ _ _ v _
| insn_ext _ _ _ v _
| insn_cast _ _ _ v _ =>
    used_in_value id' v
| insn_gep _ _ _ v vs _ =>
    used_in_value id' v || used_in_list_value id' vs
| insn_select _ v0 _ v1 v2 =>
    used_in_value id' v0 || used_in_value id' v1 || used_in_value id' v2
| insn_call _ _ _ _ _ v1 ps =>
    used_in_value id' v1 ||
    (List.fold_left (fun acc p => let '(_, v):=p in used_in_value id' v || acc)
      ps false)
end.

Definition used_in_tmn (id':id) (tmn:terminator) : bool :=
match tmn with
| insn_br _ v0 _ _ | insn_return _ _ v0 => used_in_value id' v0
| _ => false
end.

Fixpoint used_in_list_value_l (id':id) (l0:list (value * l)) : bool :=
match l0 with
| nil => false
| (v0, _) :: tl =>
    used_in_value id' v0 || used_in_list_value_l id' tl
end.

Definition used_in_phi (id':id) (pn:phinode) : bool :=
match pn with
| insn_phi _ _ vls => used_in_list_value_l id' vls
end.

Definition used_in_insn (id':id) (instr:insn) : bool :=
match instr with
| insn_cmd c => used_in_cmd id' c
| insn_phinode p => used_in_phi id' p
| insn_terminator tmn => used_in_tmn id' tmn
end.

Definition used_in_block (id':id) (b:block) : bool :=
match b with
| (_, stmts_intro ps0 cs0 tmn0) =>
  (List.fold_left (fun re p => re || used_in_phi id' p) ps0 false) ||
  (List.fold_left (fun re c => re || used_in_cmd id' c) cs0 false) ||
  (used_in_tmn id' tmn0)
end.

Definition used_in_fdef (id':id) (f:fdef) : bool :=
match f with
| fdef_intro _ bs =>
  List.fold_left (fun re b => re || used_in_block id' b) bs false
end.

(**************************************************************)
(* find all uses of a definition                              *)
Definition find_uses_in_block (id':id) (b:block) : list insn :=
let '(_, stmts_intro ps cs tmn) := b in
let is1 := 
  List.fold_left 
    (fun acc p => if used_in_phi id' p then insn_phinode p::acc else acc) 
    ps nil in
let is2 := 
  List.fold_left 
    (fun acc c => if used_in_cmd id' c then insn_cmd c::acc else acc) 
    cs is1 in
if used_in_tmn id' tmn then insn_terminator tmn::is2 else is2.

Definition find_uses_in_fdef (id':id) (f:fdef) : list insn := 
let '(fdef_intro _ bs) := f in
List.fold_left (fun acc b => find_uses_in_block id' b++acc) bs nil.

(**************************************************************)
(* Check if there exist stores that write to a location      *)
Definition store_in_cmd (id':id) (c:cmd) : bool :=
match c with
| insn_store _ _ _ ptr _ => used_in_value id' ptr
| _ => false
end.

Definition store_in_cmds (id':id) (cs:cmds) : bool :=
(List.fold_left (fun re c => re || store_in_cmd id' c) cs false).

(**************************************************************)
(* insertion                                                  *)
Definition insert_cmds (n:nat) (c:cmd) (cs : cmds) : cmds :=
firstn n cs ++ c :: skipn n cs.

(* insert c at the n-th position in block l1 *)
Definition insert_block (l1:l) (n:nat) (c:cmd) (b:block) : block :=
match b with
| (l0, stmts_intro ps0 cs0 tmn0) =>
    (l0, stmts_intro ps0 (if (l_dec l1 l0)
                          then insert_cmds n c cs0
                          else cs0) tmn0)
end.

Definition insert_fdef (l1:l) (n:nat) (c:cmd) (f:fdef) : fdef :=
let '(fdef_intro fh bs) := f in
fdef_intro fh (List.map (insert_block l1 n c) bs).

(**************************************************************)
(* renaming defs and uses                                     *)
Definition rename_id (id1:id) (id2:id) (id0:id) : id :=
if id_dec id0 id1 then id2 else id0.

Definition rename_value (id1:id) (id2:id) (v:value) : value :=
match v with
| value_id id0 => value_id (rename_id id1 id2 id0)
| _ => v
end.

Fixpoint rename_list_value (id1 id2:id) (vl:list (sz * value)) : list (sz * value) :=
match vl with
| nil => nil
| (sz0, v0) :: tl =>
    (sz0, (rename_value id1 id2 v0)) ::
      (rename_list_value id1 id2 tl)
end.

Definition rename_cmd (id1:id) (id2:id) (c:cmd) : cmd :=
match c with
| insn_bop id0 t0 bop0 v1 v2 =>
    insn_bop (rename_id id1 id2 id0) t0 bop0
      (rename_value id1 id2 v1) (rename_value id1 id2 v2)
| insn_fbop id0 fbop0 fp0 v1 v2 =>
    insn_fbop (rename_id id1 id2 id0) fbop0 fp0
      (rename_value id1 id2 v1) (rename_value id1 id2 v2)
| insn_extractvalue id0 t v cnts t' =>
    insn_extractvalue (rename_id id1 id2 id0) t (rename_value id1 id2 v) cnts t'
| insn_insertvalue id0 t1 v1 t2 v2 cnts =>
    insn_insertvalue (rename_id id1 id2 id0) t1 (rename_value id1 id2 v1) t2
      (rename_value id1 id2 v2) cnts
| insn_malloc id0 t v al =>
    insn_malloc (rename_id id1 id2 id0) t (rename_value id1 id2 v) al
| insn_free id0 t v =>
    insn_free (rename_id id1 id2 id0) t (rename_value id1 id2 v)
| insn_alloca id0 t v al =>
    insn_alloca (rename_id id1 id2 id0) t (rename_value id1 id2 v) al
| insn_load id0 t v al =>
    insn_load (rename_id id1 id2 id0) t (rename_value id1 id2 v) al
| insn_store id0 t1 v1 v2 al =>
    insn_store (rename_id id1 id2 id0) t1
      (rename_value id1 id2 v1) (rename_value id1 id2 v2) al
| insn_gep id0 ib0 t v vs t' =>
    insn_gep (rename_id id1 id2 id0) ib0 t
      (rename_value id1 id2 v) (rename_list_value id1 id2 vs) t'
| insn_trunc id0 top0 t1 v1 t2 =>
    insn_trunc (rename_id id1 id2 id0) top0 t1 (rename_value id1 id2 v1) t2
| insn_ext id0 eop0 t1 v1 t2 =>
    insn_ext (rename_id id1 id2 id0) eop0 t1 (rename_value id1 id2 v1) t2
| insn_cast id0 cop0 t1 v1 t2 =>
   insn_cast (rename_id id1 id2 id0) cop0 t1 (rename_value id1 id2 v1) t2
| insn_icmp id0 t0 cond0 v1 v2 =>
    insn_icmp (rename_id id1 id2 id0) t0 cond0
      (rename_value id1 id2 v1) (rename_value id1 id2 v2)
| insn_fcmp id0 fcond0 fp0 v1 v2 =>
    insn_fcmp (rename_id id1 id2 id0) fcond0 fp0
      (rename_value id1 id2 v1) (rename_value id1 id2 v2)
| insn_select id0 v0 t0 v1 v2 =>
    insn_select (rename_id id1 id2 id0) (rename_value id1 id2 v0) t0
      (rename_value id1 id2 v1) (rename_value id1 id2 v2)
| insn_call id0 noret0 cl0 rt1 va1 v1 ps =>
    insn_call (rename_id id1 id2 id0) noret0 cl0 rt1 va1 
      (rename_value id1 id2 v1)
      (List.map (fun p => let '(t, v):=p in (t, (rename_value id1 id2 v))) ps)
end.

Definition rename_tmn (id1:id) (id2:id) (tmn:terminator) : terminator :=
match tmn with
| insn_br id0 v0 l1 l2 =>
    insn_br (rename_id id1 id2 id0) (rename_value id1 id2 v0) l1 l2
| insn_br_uncond id0 l1 => insn_br_uncond (rename_id id1 id2 id0) l1
| insn_return id0 t0 v0 =>
    insn_return (rename_id id1 id2 id0) t0 (rename_value id1 id2 v0)
| insn_return_void id0 => insn_return_void (rename_id id1 id2 id0)
| insn_unreachable id0 => insn_unreachable (rename_id id1 id2 id0)
end.

Fixpoint rename_list_value_l (id1:id) (id2:id) (l0:list (value * l))
  : list (value * l) :=
match l0 with
| nil => nil
| (v0, l0) :: tl =>
   ((rename_value id1 id2 v0), l0) ::
     (rename_list_value_l id1 id2 tl)
end.

Definition rename_phi (id1:id) (id2:id) (pn:phinode) : phinode :=
match pn with
| insn_phi id0 t0 vls =>
    insn_phi (rename_id id1 id2 id0) t0 (rename_list_value_l id1 id2 vls)
end.

Definition rename_insn (id1:id) (id2:id) (instr:insn) : insn :=
match instr with
| insn_phinode pn => insn_phinode (rename_phi id1 id2 pn)
| insn_cmd c => insn_cmd (rename_cmd id1 id2 c)
| insn_terminator tmn => insn_terminator (rename_tmn id1 id2 tmn)
end.

Definition rename_stmts (id1:id) (id2:id) (sts:stmts) : stmts :=
match sts with
| stmts_intro ps0 cs0 tmn0 =>
  stmts_intro (List.map (rename_phi id1 id2) ps0)
    (List.map (rename_cmd id1 id2) cs0) (rename_tmn id1 id2 tmn0)
end.

Definition rename_block (id1:id) (id2:id) (b:block) : block :=
trans_block (rename_stmts id1 id2) b.

Definition rename_fheader (id1 id2:id) (fh:fheader) : fheader :=
let '(fheader_intro fr t0 fid la va):=fh in
fheader_intro fr t0 fid
  (List.map (fun a => let '(p,id0):=a in (p,rename_id id1 id2 id0)) la) va.

Definition rename_fdef (id1:id) (id2:id) (f:fdef) : fdef :=
match f with
| fdef_intro fh bs =>
    fdef_intro (rename_fheader id1 id2 fh) (List.map (rename_block id1 id2) bs)
end.

(**************************************************************)
(* renaming definitions                                        *)
Definition gen_fresh_cmd (id0:id) (c:cmd) : cmd :=
match c with
| insn_bop _ t0 bop0 v1 v2 => insn_bop id0 t0 bop0 v1 v2
| insn_fbop _ fbop0 fp0 v1 v2 => insn_fbop id0 fbop0 fp0 v1 v2
| insn_extractvalue _ t v cnts t' => insn_extractvalue id0 t v cnts t'
| insn_insertvalue _ t1 v1 t2 v2 cnts => insn_insertvalue id0 t1 v1 t2 v2 cnts
| insn_malloc _ t v al => insn_malloc id0 t v al
| insn_free _ t v => insn_free id0 t v
| insn_alloca _ t v al => insn_alloca id0 t v al
| insn_load _ t v al => insn_load id0 t v al
| insn_store _ t1 v1 v2 al => insn_store id0 t1 v1 v2 al
| insn_gep _ ib0 t v vs t' => insn_gep id0 ib0 t v vs t'
| insn_trunc _ top0 t1 v1 t2 => insn_trunc id0 top0 t1 v1 t2
| insn_ext _ eop0 t1 v1 t2 => insn_ext id0 eop0 t1 v1 t2
| insn_cast _ cop0 t1 v1 t2 => insn_cast id0 cop0 t1 v1 t2
| insn_icmp _ t0 cond0 v1 v2 => insn_icmp id0 t0 cond0 v1 v2
| insn_fcmp _ fcond0 fp0 v1 v2 => insn_fcmp id0 fcond0 fp0 v1 v2
| insn_select _ v0 t0 v1 v2 => insn_select id0 v0 t0 v1 v2
| insn_call _ noret0 cl0 rt1 va1 v1 ps => insn_call id0 noret0 cl0 rt1 va1 v1 ps
end.

(**************************************************************)
(* moving                                                     *)
Definition motion_block (l1:l) (n:nat) (newid:id) (c:cmd) (b:block) : block :=
let b1 := insert_block l1 n (gen_fresh_cmd newid c) b in
let b2 := isubst_block (getCmdLoc c) newid b1 in
let b3 := remove_block (getCmdLoc c) b2 in
rename_block newid (getCmdLoc c) b3.

Definition motion_fdef (l1:l) (n:nat) (c:cmd) (f:fdef) : fdef :=
let '(fdef_intro fh bs) := f in
let 'ex_ids := getBlocksLocs bs in
let '(exist newid _) := AtomImpl.atom_fresh_for_list ex_ids in
let f1 := insert_fdef l1 n (gen_fresh_cmd newid c) f in
let f2 := isubst_fdef (getCmdLoc c) newid f1 in
let f3 := remove_fdef (getCmdLoc c) f2 in
rename_fdef newid (getCmdLoc c) f3.

Parameter print_reachablity : list l -> bool.
Parameter print_dominators : list l -> (l -> ListSet.set l) -> bool.
Parameter print_adtree: @DTree atom -> bool.

(**************************************************************)
(* renaming labels                                            *)
Fixpoint renamel_list_value_l (l1 l2:l) (l0:list (value * l)) : list (value * l) :=
match l0 with
| nil => nil
| (v0, l0) :: tl =>
   (v0, (rename_id l1 l2 l0)) :: (renamel_list_value_l l1 l2 tl)
end.

Definition renamel_phi (l1 l2:l) (pn:phinode) : phinode :=
match pn with
| insn_phi id0 t0 vls =>
    insn_phi id0 t0 (renamel_list_value_l l1 l2 vls)
end.

Definition renamel_tmn (l1 l2:l) (tmn:terminator) : terminator :=
match tmn with
| insn_br bid c lt lf => insn_br bid c (rename_id l1 l2 lt) (rename_id l1 l2 lf)
| insn_br_uncond bid ln => insn_br_uncond bid (rename_id l1 l2 ln)
| _ => tmn
end.

Definition renamel_block (l1 l2:l) (b:block) : block := 
match b with
| (l0, stmts_intro ps0 cs0 tmn0) =>
  ((rename_id l1 l2 l0), stmts_intro (List.map (renamel_phi l1 l2) ps0) cs0 
                                        (renamel_tmn l1 l2 tmn0))
end.

Definition renamel_fdef (l1 l2:l) (f:fdef) : fdef :=
match f with
| fdef_intro fh bs =>
    fdef_intro fh (List.map (renamel_block l1 l2) bs)
end.

(**************************************************************)
(* Check if there exist loads that read from a location      *)
Definition load_in_cmd (id':id) (c:cmd) : bool :=
match c with
| insn_load _ _ v _ => used_in_value id' v
| _ => false
end.

Definition load_in_cmds (id':id) (cs:cmds) : bool :=
(List.fold_left (fun re c => re || load_in_cmd id' c) cs false).

Definition load_in_block (id':id) (b:block) : bool :=
match b with
| (_, stmts_intro _ cs0 _) => load_in_cmds id' cs0
end.

Definition load_in_fdef (id':id) (f:fdef) : bool :=
match f with
| fdef_intro _ bs =>
  List.fold_left (fun re b => re || load_in_block id' b) bs false
end.

(**************************************************************)
Lemma fdef_sim__lookupAL_stmts : forall f l0 bs sts sts',
  lookupAL _ bs l0 = Some sts ->
  lookupAL _ (List.map (trans_block f) bs) l0 = Some sts' ->
  f sts = sts'.
Proof.
  induction bs as [|a ?]; simpl; intros.
    congruence.
 
    destruct a as [l1 sts1]. simpl in *.
    destruct (l0 == l1); subst; auto.
      congruence.
Qed.

Lemma fdef_sim__lookupAL_block : forall f l0 bs sts sts',
  lookupAL _ bs l0 = Some sts ->
  lookupAL _ (List.map (trans_block f) bs) l0 = Some sts' ->
  trans_block f (l0, sts) = (l0, sts').
Proof.
  intros.
  unfold trans_block.
  f_equal.
  eapply fdef_sim__lookupAL_stmts; eauto.
Qed.

Lemma fdef_sim__lookupAL_remove_stmts : forall id0 l0 bs sts sts',
  lookupAL _ bs l0 = Some sts ->
  lookupAL _ (List.map (remove_block id0) bs) l0 = Some sts' ->
  remove_stmts id0 sts = sts'.
Proof.
  intros.
  eapply fdef_sim__lookupAL_stmts; eauto.
Qed.

Lemma fdef_sim__lookupAL_subst_stmts : forall id0 v0 l0 bs sts sts',
  lookupAL _ bs l0 = Some sts ->
  lookupAL _ (List.map (subst_block id0 v0) bs) l0 = Some sts' ->
  subst_stmts id0 v0 sts = sts'.
Proof.
  intros.
  eapply fdef_sim__lookupAL_stmts; eauto.
Qed.

(**************************************************************)
(* properties of store_in_...                                 *)
Lemma store_in_cmds_app: forall i0 cs2 cs1,
  store_in_cmds i0 (cs1++cs2) = false ->
  store_in_cmds i0 cs1 = false /\ store_in_cmds i0 cs2 = false.
Proof.
  unfold store_in_cmds.
  intros.
  rewrite fold_left_app in H.
  apply fold_left_or_false in H.
    tauto.
    intros. apply orb_false_iff in H0. tauto.
Qed.

Lemma store_in_cmds_merge: forall i0 cs1 cs2,
  store_in_cmds i0 cs1 = false /\ store_in_cmds i0 cs2 = false ->
  store_in_cmds i0 (cs1++cs2) = false.
Proof.
  unfold store_in_cmds.
  intros.
  rewrite fold_left_app.
  destruct H as [H1 H2].
  rewrite H1. auto.
Qed.

(**************************************************************)

Lemma load_notin_cmds__unused_in_value: forall vid0 id0 t v align0 cs cs11,
  load_in_cmds vid0 (cs11 ++ insn_load id0 t v align0 :: cs) = false ->
  used_in_value vid0 v = false.
Proof. 
  unfold load_in_cmds. intros.
  remember false as R. rewrite HeqR in H at 2. rewrite HeqR. clear HeqR.
  generalize dependent R. 
  induction cs11; simpl; intros; eauto.
    apply fold_left_eq in H.
      apply orb_false_iff in H.
      destruct H; auto.

      intros a b J.
      apply orb_false_iff in J.
      destruct J; auto.
Qed.

Lemma load_in_cmds_true: forall id1 id0 t align0 csb csa,
  load_in_cmds id1 (csa ++ insn_load id0 t (value_id id1) align0 :: csb) = true.
Proof.
  unfold load_in_cmds.
  intros.
  generalize false.
  induction csa; simpl; intros; eauto.
    destruct (id_dec id1 id1); try congruence. 
    simpl.
    rewrite orb_true_intro; auto.
    apply fold_left_or_spec.
    intros. subst. auto.
Qed.

Lemma load_in_cmds_app: forall i0 cs2 cs1,
  load_in_cmds i0 (cs1++cs2) = false ->
  load_in_cmds i0 cs1 = false /\ load_in_cmds i0 cs2 = false.
Proof.
  unfold load_in_cmds.
  intros.
  rewrite fold_left_app in H.
  apply fold_left_or_false in H.
    tauto.
    intros. apply orb_false_iff in H0. tauto.
Qed.

Lemma load_in_cmds_merge: forall i0 cs1 cs2,
  load_in_cmds i0 cs1 = false /\ load_in_cmds i0 cs2 = false ->
  load_in_cmds i0 (cs1++cs2) = false.
Proof.
  unfold load_in_cmds.
  intros.
  rewrite fold_left_app.
  destruct H as [H1 H2].
  rewrite H1. auto.
Qed.

Lemma load_notin_fdef__unused_in_value: forall F v t id0 align0 cs B tmn2 vid0
  (Hnld: load_in_fdef vid0 F = false) (HBinF: blockInFdefB B F = true)
  (Heq3 : exists l1 : l,
           exists ps1 : phinodes,
             exists cs11 : list cmd,
               B =
               (l1, stmts_intro ps1
                 (cs11 ++ insn_load id0 t v align0 :: cs) tmn2)),
  used_in_value vid0 v = false.
Proof.
  destruct F as [fh bs]. simpl. intros.
  remember false as R. rewrite HeqR in Hnld at 2. rewrite HeqR. clear HeqR.
  generalize dependent R. 
  induction bs; simpl in *; intros.
    inv HBinF.

    apply orb_true_iff in HBinF.
    destruct HBinF as [HBinF | HBinF]; eauto 2.
      apply blockEqB_inv in HBinF.
      subst.

      clear IHbs.
      apply fold_left_eq in Hnld.
        apply orb_false_iff in Hnld.
        destruct Hnld.
        destruct Heq3 as [l1 [ps1 [cs11 Heq3]]]; subst.
        simpl in H0.
        apply load_notin_cmds__unused_in_value in H0; auto.

        intros c b J.
        apply orb_false_iff in J.
        destruct J; auto.
Qed.

(**************************************************************)
Lemma remove_phinodes_stable: forall id' ps 
  (Hnotin: ~ In id' (getPhiNodesIDs ps)), ps = remove_phinodes id' ps.
Proof.
  induction ps; simpl; intros; auto.
    destruct_dec.
      contradict Hnotin. auto.
      simpl. rewrite <- IHps; auto.
Qed.

(**************************************************************)
(* properties of used_in_...                                  *)
Lemma used_in_blocks_cons_inv : forall bs5 id0 b5,
  fold_left (fun (re : bool) b => re || used_in_block id0 b)
    bs5 (used_in_block id0 b5) = false ->
  used_in_block id0 b5 = false /\
    fold_left (fun (re : bool) b => re || used_in_block id0 b) bs5 false
      = false.
Proof.
  intros.
  destruct (used_in_block id0 b5); auto.
    apply fold_left_eq in H.
      congruence.
      intros. binvf H0 as J1 J2; auto.
Qed.

Lemma used_in_blocks__used_in_block : forall id0 b bs,
  fold_left (fun (re : bool) (b0 : block) => re || used_in_block id0 b0) bs
    false = false ->
  InBlocksB b bs = true ->
  used_in_block id0 b = false.
Proof.
  induction bs; simpl; intros.
    congruence.

    apply used_in_blocks_cons_inv in H. destruct H.
    binvt H0 as J1 J2; auto.
      apply blockEqB_inv in J1. subst. auto.
Qed.

Lemma used_in_cmds_cons_inv : forall cs5 id0 c5
  (Hnouse : List.fold_left (fun re c => re || used_in_cmd id0 c) cs5
    (used_in_cmd id0 c5) = false),
  used_in_cmd id0 c5 = false /\
    fold_left (fun (re : bool) c => re || used_in_cmd id0 c) cs5 false = false.
Proof.
  intros.
  destruct (used_in_cmd id0 c5); auto.
    apply fold_left_eq in Hnouse.
      congruence.
      intros. binvf H as J1 J2; auto.
Qed.

Lemma used_in_cmds__used_in_cmd : forall id0 c cs,
  fold_left (fun (re : bool) c => re || used_in_cmd id0 c) cs
    false = false ->
  In c cs ->
  used_in_cmd id0 c = false.
Proof.
  induction cs; simpl; intros.
    inv H0.

    apply used_in_cmds_cons_inv in H. destruct H.
    destruct H0 as [H0 | H0]; subst; auto.
Qed.

Lemma used_in_list_value__used_in_value: forall id0 v vs,
  used_in_list_value id0 vs = false ->
  valueInListValue v vs ->
  used_in_value id0 v = false.
Proof.
  induction vs; simpl; intros.
    destruct v; auto.
      unfold valueInListValue in H0. simpl in H0. inv H0.

    simpl_prod. unfold valueInListValue in H0.
    simpl in H0.
    binvf H as J3 J4; destruct H0 as [H0 | H0]; subst; auto.
Qed.

Lemma used_in_parameters_cons_inv : forall (ps:list (typ * attributes * value))
  (id0:id) (a:typ * attributes * value)
  (Hnouse : fold_left
        (fun (acc : bool) (p : typ * attributes * value) =>
         let '(_, v) := p in used_in_value id0 v || acc) ps
        (let '(_, v) := a in used_in_value id0 v || false) = false),
  (let '(_, v) := a in used_in_value id0 v = false) /\
  fold_left
        (fun (acc : bool) (p : typ * attributes * value) =>
         let '(_, v) := p in used_in_value id0 v || acc) ps false = false.
Proof.
  intros.
  destruct a.
  destruct (used_in_value id0 v); auto.
  apply fold_left_eq in Hnouse.
    binvf Hnouse as J1 J2. congruence.

    intros. destruct b.
    binvf H as J1 J2; auto.
Qed.

Lemma valueInParams__used_in_value : forall id0 v p,
  fold_left
         (fun (acc : bool) (p : typ * attributes * value) =>
          let '(_, v) := p in used_in_value id0 v || acc) p false = false ->
  valueInParams v p ->
  used_in_value id0 v = false.
Proof.
  induction p; simpl; intros.
    destruct v; auto.
      unfold valueInParams in H0. simpl in H0. inv H0.

    apply used_in_parameters_cons_inv in H.
    destruct H as [H1 H2].
    unfold valueInParams in H0.
    destruct a. simpl in H0.
    remember (split p) as R.
    destruct R.
    simpl in H0.
    destruct H0 as [H0 | H0]; subst; auto.
    apply IHp; auto.
    unfold valueInParams. rewrite <- HeqR. auto.
Qed.

Lemma used_in_cmd__used_in_value : forall id0 v c,
  used_in_cmd id0 c = false ->
  valueInCmdOperands v c ->
  used_in_value id0 v = false.
Proof.
  induction c; simpl; intros;
    try solve [
      binvf H as J3 J4; destruct H0 as [H0 | H0]; subst; auto |
      subst; auto
    ].

    binvf H as J3 J4; destruct H0 as [H0 | H0]; subst; auto.
    eapply used_in_list_value__used_in_value; eauto.

    binvf H as J1 J2. binvf J1 as J1 J3.
    destruct H0 as [H0 | [H0 | H0]]; subst; auto.

    binvf H as J1 J2.
    destruct H0 as [H0 | H0]; subst; auto.
    eapply valueInParams__used_in_value; eauto.
Qed.

Lemma used_in_fdef__used_in_cmd_value : forall id0 l3 ps1 cs c v tmn1 F1,
  used_in_fdef id0 F1 = false ->
  blockInFdefB (l3, stmts_intro ps1 cs tmn1) F1 = true ->
  valueInCmdOperands v c -> In c cs ->
  used_in_value id0 v = false.
Proof.
  destruct F1. simpl. intros.
  eapply used_in_blocks__used_in_block in H0; eauto 2.
  binvf H0 as J3 J4. binvf J3 as J1 J2.
  eapply used_in_cmds__used_in_cmd in J2; eauto 2.
  eapply used_in_cmd__used_in_value in H1; eauto.
Qed.

Lemma used_in_tmn__used_in_value : forall id0 v tmn,
  used_in_tmn id0 tmn = false ->
  valueInTmnOperands v tmn ->
  used_in_value id0 v = false.
Proof.
  destruct tmn; simpl; intros; try solve [inv H0 | subst; auto].
Qed.

Lemma used_in_fdef__used_in_tmn_value : forall id0 l3 ps1 cs v tmn1 F1,
  used_in_fdef id0 F1 = false ->
  blockInFdefB (l3, stmts_intro ps1 cs tmn1) F1 = true ->
  valueInTmnOperands v tmn1 ->
  used_in_value id0 v = false.
Proof.
  destruct F1. simpl. intros.
  eapply used_in_blocks__used_in_block in H0; eauto 1.
  binvf H0 as J3 J4. binvf J3 as J1 J2.
  eapply used_in_tmn__used_in_value in H1; eauto 1.
Qed.

Lemma used_in_fdef__used_in_block : forall id0 b F1,
  used_in_fdef id0 F1 = false ->
  blockInFdefB b F1 = true ->
  used_in_block id0 b = false.
Proof.
  destruct F1. simpl. intros.
  eapply used_in_blocks__used_in_block in H0; eauto.
Qed.

Lemma used_in_getValueViaLabelFromValuels : forall l1 id0 l2 v
  (Hnouse : used_in_list_value_l id0 l2 = false)
  (HeqR0 : ret v = getValueViaLabelFromValuels l2 l1),
  used_in_value id0 v = false.
Proof.
  induction l2 as [|[]]; simpl; intros; try congruence.
    binvf Hnouse as J1 J2.
    destruct (l0 == l1); subst; inv HeqR0; auto.
Qed.

Lemma in_params__used: forall id1 A (t1 : A) (lp : list (A * value)) init,
  fold_left
    (fun (acc : bool) (p : A * value) =>
     let '(_, v) := p in used_in_value id1 v || acc) lp init = false ->
  ~ In (t1, value_id id1) lp.
Proof.
  induction lp as [|[]]; simpl; intros; auto.
    intro J.
    destruct J as [J | J].
      inv J.
      simpl in H.
      destruct (id_dec id1 id1); try congruence.
      simpl in H.
      rewrite fold_left_or_spec in H; try congruence.
        intros. subst. destruct b. apply orb_true_iff; auto.

      apply IHlp in H. congruence.
Qed.

Definition conditional_used_in_value (F0 F:fdef) id0 v :=
 F0 <> F \/ used_in_value id0 v = false.

Lemma conditional_used_in_fdef__used_in_tmn_value: forall (l3 : l)
  (ps1 : phinodes) (cs : cmds) (v : value) (tmn1 : terminator) (F: fdef) F0 id0,
  used_in_fdef id0 F0 = false ->
  blockInFdefB (l3, stmts_intro ps1 cs tmn1) F = true ->
  valueInTmnOperands v tmn1 ->
  conditional_used_in_value F0 F id0 v.
Proof.
  intros.
  unfold conditional_used_in_value.
  destruct (fdef_dec F0 F); subst; auto.
    right. eapply used_in_fdef__used_in_tmn_value; eauto; simpl; auto.
Qed.

Lemma conditional_used_in_fdef__used_in_cmd_value: forall (l3 : l) c
  (ps1 : phinodes) (cs : cmds) (v : value) (tmn1 : terminator) (F: fdef) F0 id0,
  used_in_fdef id0 F0= false ->
  blockInFdefB (l3, stmts_intro ps1 cs tmn1) F = true ->
  In c cs ->
  valueInCmdOperands v c ->
  conditional_used_in_value F0 F id0 v.
Proof.
  intros.
  unfold conditional_used_in_value.
  destruct (fdef_dec F0 F); subst; auto.
    right. eapply used_in_fdef__used_in_cmd_value; eauto; simpl; auto.
Qed.

Lemma conditional_used_in_getValueViaLabelFromValuels: forall F0 id0 F l3 l0 v
  (Hnuse : F0 <> F \/ used_in_list_value_l id0 l0 = false)
  (HeqR3 : getValueViaLabelFromValuels l0 l3 = ret v),
  conditional_used_in_value F0 F id0 v.
Proof.
  intros.
  unfold conditional_used_in_value.
  destruct (fdef_dec F0 F); subst; auto.
  destruct Hnuse as [Hnuse | Hnuse]; try congruence.
  right.
  eapply used_in_getValueViaLabelFromValuels; eauto.
Qed.

Definition conditional_used_in_list_value (F0 F:fdef) id0 idxs :=
  F0 <> F \/ used_in_list_value id0 idxs = false.

Lemma conditional_used_in_fdef__used_in_list_value: forall (l3 : l)
  (ps1 : phinodes) (cs : cmds) (v : value) (tmn1 : terminator) (F: fdef) F0 id1
  cs11 id0 inbounds0 t v idxs cs t',
  used_in_fdef id1 F0 = false ->
  blockInFdefB
    (l3, stmts_intro ps1 (cs11 ++ insn_gep id0 inbounds0 t v idxs t':: cs) tmn1) F
      = true ->
  conditional_used_in_list_value F0 F id1 idxs.
Proof.
  intros.
  unfold conditional_used_in_list_value.
  destruct (fdef_dec F0 F); subst; auto.
    right.
    destruct F. simpl in *.
    eapply used_in_blocks__used_in_block in H0; eauto 1.
    binvf H0 as J3 J4. binvf J3 as J1 J2.
    eapply used_in_cmds__used_in_cmd in J2; eauto 1 using in_middle.
    simpl in J2.
    binvf J2 as J3 J5. auto.
Qed.

Definition conditional_used_in_params (F0 F:fdef) id0 (ps:params) :=
  F0 <> F \/
  List.fold_left
    (fun acc p => let '(_, v):=p in used_in_value id0 v || acc)
    ps false = false.

Lemma conditional_used_in_fdef__used_in_params: forall (l3 : l)
  (ps1 : phinodes) (cs : cmds) (v : value) (tmn1 : terminator) (F: fdef) F0 id0
  cs11 rid noret0 ca rt1 va1 fv lp cs,
  used_in_fdef id0 F0 = false ->
  blockInFdefB
    (l3, stmts_intro ps1 (cs11 ++ insn_call rid noret0 ca rt1 va1 fv lp :: cs) tmn1) F
      = true ->
  conditional_used_in_params F0 F id0 lp.
Proof.
  intros.
  unfold conditional_used_in_params.
  destruct (fdef_dec F0 F); subst; auto.
    right.
    destruct F. simpl in *.
    eapply used_in_blocks__used_in_block in H0; eauto 1.
    binvf H0 as J3 J4. binvf J3 as J1 J2.
    eapply used_in_cmds__used_in_cmd in J2; eauto 1 using in_middle.
    simpl in J2.
    binvf J2 as J3 J5. auto.
Qed.

Lemma conditional_used_in_fdef__used_in_phis: forall (l3 : l)
  (ps1 : phinodes) (cs : cmds) (tmn1 : terminator) (F: fdef) F0 id0 cs1,
  used_in_fdef id0 F0 = false ->
  blockInFdefB (l3, stmts_intro ps1 cs1 tmn1) F = true ->
  F0 <> F \/
  fold_left
         (fun (re : bool) (p : phinode) => re || used_in_phi id0 p)
         ps1 false = false.
Proof.
  intros.
  destruct (fdef_dec F0 F); subst; auto.
    right.
    destruct F. simpl in *.
    eapply used_in_blocks__used_in_block in H0; eauto 1.
    binvf H0 as J3 J4. binvf J3 as J1 J2. auto.
Qed.

Definition conditional_used_in_args (F0 F:fdef) id0 
  (la:list (typ * attributes * id)) :=
  F0 <> F \/ (forall t a i0, In (t,a,i0) la -> id0 <> i0).

Hint Unfold conditional_used_in_value conditional_used_in_list_value 
  conditional_used_in_params conditional_used_in_args.

Lemma used_in_list_value_l_false__intro: forall id0 vls 
  (H: forall v0 l0, In (v0, l0) vls -> used_in_value id0 v0 = false),
  used_in_list_value_l id0 vls = false.
Proof.
  induction vls as [|[]]; simpl; intros; auto.
    apply orb_false_intro; eauto.
Qed.

Lemma valueEqB__used_in_value: forall pid v,
  valueEqB v (value_id pid) = used_in_value pid v.
Proof.
  intros. unfold valueEqB. 
  destruct (value_dec v (value_id pid)); subst; simpl.
    destruct_dec.
    destruct v; simpl; auto.
      destruct_dec.
Qed.

Lemma noused_values2ids : forall id' l0
  (H2 : used_in_list_value_l id' l0 = false),
  ~ In id' (values2ids (list_prj1 value l l0)).
Proof.
  intros.
  induction l0 as [|[v]]; simpl; intros; auto.
    destruct v; simpl in *; auto.
    binvf H2 as H1 H2; subst; auto.
    apply IHl0 in H2.
    intro J.
    destruct J as [J | J]; subst; auto.
      apply not_id_dec__neq in H1; auto.
Qed.

Lemma noused_getPhiNodeOperands : forall id' p
  (H2 :used_in_phi id' p = false),
  ~ In id' (getPhiNodeOperands p).
Proof.
  destruct p; simpl; intros. auto using noused_values2ids.
Qed.

Lemma noused_getCmdOperands : forall id' c
  (H2 : used_in_cmd id' c = false),
  ~ In id' (getCmdOperands c).
Proof.
  intros.
  intro J.
  apply used_in_cmd__used_in_value with (v:=value_id id') in H2; auto.
    simpl in H2. destruct_dec. 
    apply InOps__valueInCmdOperands; auto.
Qed.

Lemma noused_getTerminatorOperands : forall id' t
  (H2 : used_in_tmn id' t = false),
  ~ In id' (getTerminatorOperands t).
Proof.
  intros.
  intro J.
  apply used_in_tmn__used_in_value with (v:=value_id id') in H2; auto.
    simpl in H2. destruct_dec. 
    apply InOps__valueInTmnOperands; auto.
Qed.

Lemma noused_getInsnOperands : forall id' instr
  (H2 : used_in_insn id' instr = false),
  ~ In id' (getInsnOperands instr).
Proof.
  destruct instr; simpl; auto 
    using noused_getPhiNodeOperands,
          noused_getCmdOperands, noused_getTerminatorOperands.
Qed.

Lemma used_in_phinodes_cons_inv : forall phinodes5 id0 phinode5,
  fold_left (fun (re : bool) (p : phinode) => re || used_in_phi id0 p)
    phinodes5 (used_in_phi id0 phinode5) = false ->
  used_in_phi id0 phinode5 = false /\
    fold_left (fun (re : bool) (p : phinode) => re || used_in_phi id0 p)
      phinodes5 false = false.
Proof.
  intros.
  destruct (used_in_phi id0 phinode5); auto.
    apply fold_left_eq in H.
      congruence.
      intros. binvf H0 as J1 J2; auto.
Qed.

Lemma used_in_fdef_elim: forall id5 f (Huse: used_in_fdef id5 f = true),
  exists instr, exists b,
    insnInFdefBlockB instr f b = true /\ used_in_insn id5 instr.
Proof.
  destruct f as [fh bs]. simpl. intros.
  apply fold_left_or_true_elim in Huse.
  destruct Huse as [x [Hin Huse]].
  destruct x as [l0 [ps0 cs0 tmn0]].
  simpl in Huse.
  binvt Huse as J1 J2.
    binvt J1 as J3 J2.
      apply fold_left_or_true_elim in J3.
      destruct J3 as [x [J3 Huse]].
      exists (insn_phinode x). exists (l0,stmts_intro ps0 cs0 tmn0).
      split; auto.
      simpl. 
      bsplit; solve_in_list; auto.

      apply fold_left_or_true_elim in J2.
      destruct J2 as [x [J3 Huse]].
      exists (insn_cmd x). exists (l0,stmts_intro ps0 cs0 tmn0).
      split; auto.
      simpl. 
      bsplit; solve_in_list; auto.
    exists (insn_terminator tmn0). exists (l0,stmts_intro ps0 cs0 tmn0).
    split; auto.
    simpl. 
    bsplit. solve_refl. solve_in_list; auto.
Qed.

Lemma used_in_list_value_l__values2ids: forall (id5 : id) (l0 : list (value * l))
  (Huse: used_in_list_value_l id5 l0),
  In id5 (values2ids (list_prj1 value l l0)).
Proof.
  induction l0 as [|[v]]; simpl; intros.
    congruence.

    destruct v; auto. 
    simpl.
    binvt Huse as J1 J2; auto.
      simpl in J1. destruct_dec.
Qed.

Lemma used_in_insn__getPhiNodeOperands: forall (id5 : id) (phinode5 : phinode)
  (Huse : used_in_insn id5 (insn_phinode phinode5)),
  In id5 (getPhiNodeOperands phinode5).
Proof.
  destruct phinode5. simpl. apply used_in_list_value_l__values2ids; auto.
Qed.

Lemma used_in_value__getValueIDs: forall (id5:id) (value1:value)
  (Huse: used_in_value id5 value1),
  In id5 (infrastructure.LLVMinfra.getValueIDs value1).
Proof.
  destruct value1; simpl; intros.
    destruct_dec.
    congruence.
Qed.

Lemma used_in_list_value__values2ids: forall (id5 : id) l0
  (Huse: used_in_list_value id5 l0),
  In id5 (values2ids (List.map snd l0)).
Proof.
  induction l0 as [|[]]; simpl; intros.
    congruence.

    destruct v; auto. 
    simpl.
    binvt Huse as J1 J2; auto.
      simpl in J1. destruct_dec.
Qed.

Lemma used_in_params__getParamsOperand: forall (id5 : id) l0 init
  (Huse : fold_left
            (fun (acc : bool) (p : typ * attributes * value) =>
             let '(_, v) := p in used_in_value id5 v || acc) l0 init =
          true),
  In id5 (getParamsOperand l0) \/ init = true.
Proof.
  unfold getParamsOperand.
  induction l0 as [|[[] v]]; simpl; intros; auto.
    destruct_let. simpl.
    destruct v; auto.
      simpl. 
      apply IHl0 in Huse.
      destruct Huse as [Huse | Huse]; auto.
      binvt Huse as J1 J2; auto.
      simpl in J1. destruct_dec.
Qed.

Lemma used_in_insn__getCmdOperands: forall (id5 : id) (cmd5 : cmd) 
  (Huse : used_in_insn id5 (insn_cmd cmd5)),
  In id5 (getCmdOperands cmd5).
Proof.
  destruct cmd5; simpl; try solve [
    auto |
    intro; apply used_in_value__getValueIDs in Huse; auto |
    intro; 
      match goal with
      | |- In _ (_++_) =>
       apply in_or_app;
        binvt Huse as J1 Huse; try solve [
          apply used_in_value__getValueIDs in J1; auto |
          apply used_in_value__getValueIDs in Huse; auto |
          apply used_in_list_value__values2ids in Huse; auto
        ]
      end
  ].

    intro.
    apply in_or_app.
    binvt Huse as Huse Huse.
      binvt Huse as Huse Huse.
        apply used_in_value__getValueIDs in Huse; auto.

        right. apply in_or_app.
        apply used_in_value__getValueIDs in Huse; auto.
      right. apply in_or_app.
      apply used_in_value__getValueIDs in Huse; auto.

    intro.
    apply in_or_app.
    binvt Huse as Huse Huse.
      apply used_in_value__getValueIDs in Huse; auto.

      apply used_in_params__getParamsOperand in Huse.
      destruct Huse; try congruence; auto.
Qed.

Lemma used_in_insn__getTerminatorOperands: forall (id5 : id) (tmn5 : terminator) 
  (Huse : used_in_insn id5 (insn_terminator tmn5)),
  In id5 (getTerminatorOperands tmn5).
Proof.
  destruct tmn5; simpl; intro; try solve [
    auto |
    congruence |
    apply used_in_value__getValueIDs in Huse; auto |
    match goal with
    | |- In _ (_++_) =>
       apply in_or_app;
        binvt Huse as J1 Huse; try solve [
          apply used_in_value__getValueIDs in J1; auto |
          apply used_in_value__getValueIDs in Huse; auto
        ]
    end
  ].
Qed.

Lemma used_in_insn__valueInInsnOperands: forall id5 instr
  (Huse : used_in_insn id5 instr), valueInInsnOperands (value_id id5) instr.
Proof.
  intros.
  apply InOps__valueInInsnOperands; auto.
  destruct instr; simpl.
    apply used_in_insn__getPhiNodeOperands; auto.
    apply used_in_insn__getCmdOperands; auto.
    apply used_in_insn__getTerminatorOperands; auto.
Qed.

(*********************************************************)
(*           used w.r.t reachability                     *)

Lemma used_in_value_inv: forall id0 v (Hused: used_in_value id0 v = true), 
  v = value_id id0.
Proof.
  intros.
  destruct v as [vid|]; inv Hused.
  destruct_dec.
Qed.

Section IdInReachableBlock.

Variable (S:system) (M:module) (F1:fdef) (id0:id).
Hypothesis (Huniq: uniqFdef F1) (HwfF: wf_fdef S M F1).

(* subst.v should use this lemma in isubst_wf_operand *)
Lemma insnOrBlockStrictDominates__id_in_reachable_block: forall b b0
  (Hreach : isReachableFromEntry F1 b) instr
  (HBinF: blockInFdefB b F1 = true) 
  (Hlk: lookupBlockViaIDFromFdef F1 id0 = Some b0)
  (J2 : insnDominates id0 instr b \/ blockStrictDominates F1 b0 b),
  id_in_reachable_block F1 id0.
Proof.
  intros. 
  intros b' Hlkup. uniq_result.
  destruct J2 as [H4 | H4].
    eapply insnDominates_spec3 in H4; eauto 1.
    uniq_result. auto.

    eapply blockStrictDominates_isReachableFromEntry; eauto.
Qed.

Lemma reachable_used_in_operand__id_in_reachable_block: forall b instr 
  (HBinF: blockInFdefB b F1 = true) 
  (Hreach : isReachableFromEntry F1 b) (Hop: wf_operand F1 b instr id0),
  id_in_reachable_block F1 id0 \/ In id0 (getArgsIDsOfFdef F1).
Proof.
  intros.
  inv Hop.
  match goal with
  | H3: (_ \/ _) \/ _ |- _ => 
    destruct H3 as [[[b0 [J1 J2]] | H3] | H3]; try solve [auto | congruence]
  end.
    left. eapply insnOrBlockStrictDominates__id_in_reachable_block; eauto.
Qed.

Lemma reachable_used_in_insn__id_in_reachable_block: forall b instr 
  (Hreach : isReachableFromEntry F1 b) (HBinF : blockInFdefB b F1 = true)
  v (HinOps : valueInInsnOperands v instr)
  (Hused: used_in_value id0 v = true)
  (Hwfc : wf_insn_base F1 b instr),
  id_in_reachable_block F1 id0 \/ In id0 (getArgsIDsOfFdef F1).
Proof.
  intros.
  inv Hwfc.
  apply used_in_value_inv in Hused. subst.
  apply valueInInsnOperands__InOps in HinOps.
  eapply reachable_used_in_operand__id_in_reachable_block; eauto 1.
  rewrite map_id in H2.
  eapply H2; eauto.
Qed.

Lemma reachable_used_in_cmd_value__id_in_reachable_block : forall l3 ps1 cs c v 
  tmn1 (Hreach: isReachableFromEntry F1 (l3, stmts_intro ps1 cs tmn1))
  (HBinF: blockInFdefB (l3, stmts_intro ps1 cs tmn1) F1 = true )
  (HinOps: valueInCmdOperands v c) (HinCs: In c cs)
  (Hused: used_in_value id0 v = true),
  id_in_reachable_block F1 id0 \/ In id0 (getArgsIDsOfFdef F1).
Proof.
  intros.
  assert (Hwfc:=HBinF).
  eapply wf_fdef__wf_cmd in Hwfc; eauto 1.
  apply wf_insn__wf_insn_base in Hwfc; try solve [auto | solve_isNotPhiNode].
  eapply reachable_used_in_insn__id_in_reachable_block; eauto; simpl; auto.
Qed.

Lemma reachable_used_in_tmn_value__id_in_reachable_block : forall l3 ps1 cs v 
  tmn1 (Hreach: isReachableFromEntry F1 (l3, stmts_intro ps1 cs tmn1))
  (HBinF: blockInFdefB (l3, stmts_intro ps1 cs tmn1) F1 = true )
  (HinOps: valueInTmnOperands v tmn1) 
  (Hused: used_in_value id0 v = true),
  id_in_reachable_block F1 id0 \/ In id0 (getArgsIDsOfFdef F1).
Proof.
  intros.
  assert (Hwfc:=HBinF).
  eapply wf_fdef__wf_tmn in Hwfc; eauto 1.
  apply wf_insn__wf_insn_base in Hwfc; try solve [auto | solve_isNotPhiNode].
  eapply reachable_used_in_insn__id_in_reachable_block; eauto; simpl; auto.
Qed.

Lemma reachable_used_in_incoming_value__id_in_reachable_block: forall b pn b0
  (Hreach: isReachableFromEntry F1 b0) (HBinF: blockInFdefB b0 F1 = true)
  (Hwfpn: wf_phinode F1 b pn) v
  (Hget: getValueViaBlockFromPHINode pn b0 = Some v)
  (Hused: used_in_value id0 v = true),
  id_in_reachable_block F1 id0 \/ In id0 (getArgsIDsOfFdef F1).
Proof.
  intros. destruct pn.
  destruct Hwfpn as [Hwfpi _].
  destruct b0 as [? []].
  simpl in Hget.
  apply used_in_value_inv in Hused. subst.
  apply getValueViaLabelFromValuels__nth_list_value_l in Hget.
  destruct Hget as [n Hget].
  eapply wf_phi_operands__elim in Hget; eauto.
  destruct Hget as [b1 [Hlk [Hget | Hget]]]; auto.
  left.
  assert (Hlkup:=HBinF).
  apply blockInFdefB_lookupBlockViaLabelFromFdef in Hlkup; auto.
  uniq_result. 
  destruct Hget as [[b' [J1 J2]] | Hget]; try (simpl in *; congruence).
    intros b'' Hlkup''. uniq_result. 
    eapply blockDominates_isReachableFromEntry; eauto.
Qed.

Lemma reachable_used_in_incoming_values__id_in_reachable_block: forall l3 ps1 cs 
  tmn1 pn b0
  (Hreach: isReachableFromEntry F1 b0) (HBinF0: blockInFdefB b0 F1 = true)
  (HBinF: blockInFdefB (l3, stmts_intro ps1 cs tmn1) F1 = true ) v
  (Hget: getValueViaBlockFromPHINode pn b0 = Some v) (Hin: In pn ps1)
  (Hused: used_in_value id0 v = true),
  id_in_reachable_block F1 id0 \/ In id0 (getArgsIDsOfFdef F1).
Proof.
  intros.
  eapply wf_fdef__wf_phinodes in HBinF; eauto.
  eapply wf_phinodes__wf_phinode in HBinF; eauto.
  inv HBinF.
  eapply reachable_used_in_incoming_value__id_in_reachable_block; eauto.
Qed.

End IdInReachableBlock.

Ltac destruct_bgoal := 
match goal with
| |- ?e = false =>
     remember e as R; destruct R; auto
end.

Section ReachableUnUse.

Definition runused_in_fdef (id0:id) (F1:fdef) : Prop :=
  id_in_reachable_block F1 id0 \/ In id0 (getArgsIDsOfFdef F1) -> 
  used_in_fdef id0 F1 = false.

Definition runused_in_phi F1 (id0:id) (pn:phinode) : Prop :=
  id_in_reachable_block F1 id0 \/ In id0 (getArgsIDsOfFdef F1) -> 
  used_in_phi id0 pn = false.

Variable (S:system) (M:module) (F1:fdef) (id0:id).
Hypothesis (Huniq: uniqFdef F1) (HwfF: wf_fdef S M F1).

Lemma runused_in_fdef__used_in_cmd_value : forall l3 ps1 cs c v tmn1
  (Hreach: isReachableFromEntry F1 (l3, stmts_intro ps1 cs tmn1))
  (Hruse: runused_in_fdef id0 F1)
  (HbInF: blockInFdefB (l3, stmts_intro ps1 cs tmn1) F1 = true)
  (HinOps: valueInCmdOperands v c) (HinCs: In c cs),
  used_in_value id0 v = false.
Proof.
  intros.
  destruct_bgoal.
  eapply reachable_used_in_cmd_value__id_in_reachable_block in Hreach; eauto 1.
  apply Hruse in Hreach.
  eapply used_in_fdef__used_in_cmd_value in Hreach; eauto.
Qed.

Lemma runused_in_fdef__used_in_tmn_value : forall l3 ps1 cs v tmn1 
  (Hreach: isReachableFromEntry F1 (l3, stmts_intro ps1 cs tmn1))
  (Hruse: runused_in_fdef id0 F1)
  (HbInF: blockInFdefB (l3, stmts_intro ps1 cs tmn1) F1 = true)
  (HinOpse: valueInTmnOperands v tmn1),
  used_in_value id0 v = false.
Proof.
  intros.
  destruct_bgoal.
  eapply reachable_used_in_tmn_value__id_in_reachable_block in Hreach; eauto 1.
  apply Hruse in Hreach.
  eapply used_in_fdef__used_in_tmn_value in Hreach; eauto.
Qed.

Lemma runused_in_fdef__used_in_getValueViaBlockFromPHINode : forall pn b0
  l3 ps1 cs tmn1
  (Hreach: isReachableFromEntry F1 b0) (HBinF0: blockInFdefB b0 F1 = true)
  (HBinF: blockInFdefB (l3, stmts_intro ps1 cs tmn1) F1 = true ) v
  (Hget: getValueViaBlockFromPHINode pn b0 = Some v) 
  (Hin: In pn ps1)
  (Hruse : runused_in_fdef id0 F1),
  used_in_value id0 v = false.
Proof.
  intros.
  destruct_bgoal.
  eapply reachable_used_in_incoming_values__id_in_reachable_block in Hreach; 
    eauto 1.
  apply Hruse in Hreach.
  destruct b0, pn. simpl in *.
    eapply used_in_fdef__used_in_block in Hreach; eauto 1.
    binvf Hreach as J3 J4. binvf J3 as J1 J2. 
    eapply fold_left_or_false_elim in J1; eauto 1.
    eapply used_in_getValueViaLabelFromValuels in J1; eauto.
Qed.

End ReachableUnUse.

Lemma used_in_list_value__valuesInListValue: forall (id5 : id) l0
  (Huse: used_in_list_value id5 l0 = true), valueInListValue (value_id id5) l0.
Proof.
  unfold valueInListValue.
  induction l0 as [|[]]; simpl; intros.
    congruence.

    destruct v; simpl; auto. 
    binvt Huse as J1 J2; auto.
      simpl in J1. destruct_dec.
Qed.

Lemma used_in_value__valueInParams: forall id0 lp
  (HeqR : true =
         fold_left
           (fun (acc : bool) (p : typ * attributes * value) =>
            let '(_, v) := p in used_in_value id0 v || acc) lp false),
  valueInParams (value_id id0) lp.
Proof.
  unfold valueInParams.
  induction lp as [|[[]v]]; simpl; intros.
    congruence.

    destruct_let. 
    simpl. symmetry in HeqR.
    remember (used_in_value id0 v|| false) as R.
    destruct R.
      symmetry in HeqR0.
      apply orb_true_iff in HeqR0.
      destruct HeqR0 as [HeqR0 | HeqR0]; try congruence.
        apply used_in_value_inv in HeqR0. auto.
        right. eauto.   
Qed.

Section ConditionalReachableUnUse.

Variable (S:system) (M:module) (F F0:fdef) (id0:id).
Hypothesis (Huniq: uniqFdef F) (HwfF: wf_fdef S M F).

Lemma conditional_runused_in_fdef__used_in_tmn_value: forall (l3 : l)
  (ps1 : phinodes) (cs : cmds) (v : value) (tmn1 : terminator)
  (Hreach: isReachableFromEntry F (l3, stmts_intro ps1 cs tmn1))
  (Hruse: runused_in_fdef id0 F0),
  blockInFdefB (l3, stmts_intro ps1 cs tmn1) F = true ->
  valueInTmnOperands v tmn1 ->
  conditional_used_in_value F0 F id0 v.
Proof.
  intros.
  unfold conditional_used_in_value.
  destruct (fdef_dec F0 F); subst; auto.
    right. eapply runused_in_fdef__used_in_tmn_value; eauto; simpl; auto.
Qed.

Lemma conditional_runused_in_fdef__used_in_cmd_value: forall (l3 : l) c
  (ps1 : phinodes) (cs : cmds) (v : value) (tmn1 : terminator)
  (Hreach: isReachableFromEntry F (l3, stmts_intro ps1 cs tmn1)),
  runused_in_fdef id0 F0 ->
  blockInFdefB (l3, stmts_intro ps1 cs tmn1) F = true ->
  In c cs ->
  valueInCmdOperands v c ->
  conditional_used_in_value F0 F id0 v.
Proof.
  intros.
  unfold conditional_used_in_value.
  destruct (fdef_dec F0 F); subst; auto.
    right. eapply runused_in_fdef__used_in_cmd_value; eauto; simpl; auto.
Qed.

Lemma conditional_runused_in_fdef__used_in_getValueViaBlockFromPHINode : forall pn b0
  l3 ps1 cs tmn1
  (Hreach: isReachableFromEntry F b0) (HBinF0: blockInFdefB b0 F = true)
  (HBinF: blockInFdefB (l3, stmts_intro ps1 cs tmn1) F = true ) v
  (Hget: getValueViaBlockFromPHINode pn b0 = Some v) 
  (Hin: In pn ps1)
  (Hruse : runused_in_fdef id0 F0),
  conditional_used_in_value F0 F id0 v.
Proof.
  intros.
  unfold conditional_used_in_value.
  destruct (fdef_dec F0 F); subst; auto.
    right. 
    eapply runused_in_fdef__used_in_getValueViaBlockFromPHINode; eauto; simpl; auto.
Qed.

Lemma conditional_runused_in_fdef__used_in_list_value: forall (l3 : l)
  (ps1 : phinodes) (cs : cmds) (v : value) (tmn1 : terminator)
  cs11 inbounds0 t v idxs cs t' id1
  (Hreach: isReachableFromEntry F 
    (l3, stmts_intro ps1 (cs11 ++ insn_gep id1 inbounds0 t v idxs t':: cs) tmn1)),
  runused_in_fdef id0 F0 ->
  blockInFdefB
    (l3, stmts_intro ps1 (cs11 ++ insn_gep id1 inbounds0 t v idxs t':: cs) tmn1) F
      = true ->
  conditional_used_in_list_value F0 F id0 idxs.
Proof.
  intros.
  unfold conditional_used_in_list_value.
  destruct (fdef_dec F0 F); subst; auto.
    right.
    destruct_bgoal.
    eapply runused_in_fdef__used_in_cmd_value with (v:=value_id id0) in H0; 
      eauto 2 using in_middle.
      simpl in H0. destruct_dec.
 
      right. apply used_in_list_value__valuesInListValue; auto.
Qed.

Lemma conditional_runused_in_fdef__used_in_params: forall (l3 : l)
  (ps1 : phinodes) (cs : cmds) (v : value) (tmn1 : terminator)
  cs11 rid noret0 ca rt1 va1 fv lp cs
  (Hreach: isReachableFromEntry F 
    (l3, stmts_intro ps1 (cs11 ++ insn_call rid noret0 ca rt1 va1 fv lp :: cs) tmn1)),
  runused_in_fdef id0 F0 ->
  blockInFdefB
    (l3, stmts_intro ps1 (cs11 ++ insn_call rid noret0 ca rt1 va1 fv lp :: cs) tmn1) F
      = true ->
  conditional_used_in_params F0 F id0 lp.
Proof.
  intros.
  unfold conditional_used_in_params.
  destruct (fdef_dec F0 F); subst; auto.
    right.
    destruct_bgoal.
    eapply runused_in_fdef__used_in_cmd_value with (v:=value_id id0) in H0; 
      eauto 2 using in_middle.
      simpl in H0. destruct_dec.
 
      right. apply used_in_value__valueInParams; auto.
Qed.

End ConditionalReachableUnUse.

Section SubstUnused.

Variable (id1:id) (v1:value).
Hypothesis (Hnotin: ~ In id1 (getValueIDs v1)).

Lemma notin_unused_in_value:
  used_in_value id1 v1 = false.
Proof.
  destruct v1; simpl in *; intros; auto.
    destruct_dec; subst; simpl; auto.
      contradict Hnotin; auto.
Qed.

Lemma subst_unused_in_value: forall v,
  used_in_value id1 (v {[v1 // id1]}) = false.
Proof.
  destruct v; simpl; intros; auto.
    destruct_dec.
      rewrite notin_unused_in_value; auto.
      simpl. destruct_dec.
Qed.

Lemma subst_unused_in_vls: forall vls,
  used_in_list_value_l id1 (subst_list_value_l id1 v1 vls) = false.
Proof.
  induction vls as [|[v]]; simpl; intros; auto.
    apply orb_false_iff.
    split; auto using subst_unused_in_value.
Qed.

Lemma subst_unused_in_phinodes: forall ps,
  fold_left (fun (re : bool) (p0 : phinode) => re || used_in_phi id1 p0)
     (List.map (subst_phi id1 v1) ps) false = false.
Proof.
  induction ps as [|[]]; simpl; intros; auto.
    rewrite subst_unused_in_vls; auto.
Qed.

Lemma subst_unused_in_vs: forall vs,
  used_in_list_value id1 (subst_list_value id1 v1 vs) = false.
Proof.
  induction vs as [|[v]]; simpl; intros; auto.
    apply orb_false_iff.
    split; auto using subst_unused_in_value.
Qed.

Lemma subst_unused_in_cmd: forall c,
  used_in_cmd id1 (subst_cmd id1 v1 c) = false.
Proof.
  destruct c; simpl; try solve [
    auto using subst_unused_in_value |
    repeat (apply orb_false_iff;
              split; auto using subst_unused_in_value, subst_unused_in_vs)
  ].

    apply orb_false_iff.
    split; auto using subst_unused_in_value.
      induction params5 as [|[[]]]; simpl; auto.
        rewrite subst_unused_in_value; auto.
Qed.

Lemma subst_unused_in_cmds: forall cs,
  fold_left (fun (re : bool) (c0 : cmd) => re || used_in_cmd id1 c0)
     (List.map (subst_cmd id1 v1) cs) false = false.
Proof.
  induction cs; simpl; intros; auto.
    rewrite subst_unused_in_cmd; auto.
Qed.

Lemma subst_unused_in_tmn: forall t,
  used_in_tmn id1 (subst_tmn id1 v1 t) = false.
Proof.
  destruct t; simpl; auto using subst_unused_in_value.
Qed.

Lemma subst_unused_in_block: forall b,
  used_in_block id1 (subst_block id1 v1 b) = false.
Proof.
  destruct b as [? []]. simpl. 
  rewrite subst_unused_in_phinodes; auto.
  rewrite subst_unused_in_cmds; auto.
  rewrite subst_unused_in_tmn; auto.
Qed.

Lemma subst_unused_in_fdef: forall f,
  used_in_fdef id1 (subst_fdef id1 v1 f) = false.
Proof.
  destruct f as [fh bs]. simpl.
  intros.
  induction bs; simpl; auto.
    rewrite subst_unused_in_block; auto.
Qed.

End SubstUnused.

Lemma used_in_phi_fun_spec: forall pid (a0 : bool) (b : phinode),
  a0 || used_in_phi pid b = false -> a0 = false.
Proof.
  intros. apply orb_false_iff in H. destruct H; auto.
Qed.

Lemma unused_in_phis__unused_in_phi: forall (pid id0 : id) (ps : phinodes)
  (p0 : phinode) (J1 : ret p0 = lookupPhiNodeViaIDFromPhiNodes ps id0)
  (J2 : fold_left (fun (re : bool) (p : phinode) => re || used_in_phi pid p)
          ps false = false),
  used_in_phi pid p0 = false.
Proof.
  induction ps; simpl; intros.
    congruence.

    assert (fold_left (fun (re : bool) (p : phinode) => re || used_in_phi pid p)
              ps false = false /\ used_in_phi pid a = false) as J3.
      apply fold_left_or_false; auto.
        apply used_in_phi_fun_spec.

    destruct J3 as [J3 J4].
    destruct (getPhiNodeID a == id0); subst; eauto.
      inv J1. auto.
Qed.

Lemma unused_in_value__neg_valueEqB: forall pid v,
  used_in_value pid v = false ->
  negb (valueEqB v (value_id pid)).
Proof.
  intros.
  unfold valueEqB.
  destruct v as [i0|c]; inv H; simpl.
    destruct (value_dec (value_id i0) (value_id pid)); simpl.
      inversion e. subst.
      destruct (id_dec pid pid); subst; inv H1; try congruence.

      reflexivity.

    destruct (value_dec (value_const c) (value_id pid)); simpl.
      congruence.
      reflexivity.
Qed.

Lemma used_in_cmd_fun_spec:
  forall pid acc0 c,
  (if used_in_cmd pid c then
    match c with
    | insn_load _ _ _ _ => acc0
    | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) && acc0
    | _ => false
    end
  else acc0) = true -> acc0 = true.
Proof.
  intros. clear - H.
  destruct acc0; auto.
  destruct (used_in_cmd pid c); auto.
  destruct c; auto.
  apply andb_true_iff in H. destruct H; auto.
Qed.

Lemma unused_in_cmds__unused_in_cmd: forall (pid id0 : id) (cs : cmds)
  (c0 : cmd) (J1 : ret c0 = lookupCmdViaIDFromCmds cs id0)
  (J2 : fold_left
          (fun acc0 c =>
           if used_in_cmd pid c then
             match c with
             | insn_load _ _ _ _ => acc0
             | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) && acc0
             | _ => false
             end
           else acc0) cs true = true),
  match c0 with
  | insn_load _ _ _ _ => True
  | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid))
  | _ => used_in_cmd pid c0 = false
  end.
Proof.
  induction cs; simpl; intros.
    congruence.

    assert (
      fold_left
        (fun acc0 c =>
         if used_in_cmd pid c then
           match c with
           | insn_load _ _ _ _ => acc0
           | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) && acc0
           | _ => false
           end
         else acc0) cs true = true /\
      (if used_in_cmd pid a then
         match a with
         | insn_load _ _ _ _ => true
         | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) && true
         | _ => false
         end
       else true) = true) as J3.
      apply fold_left_and_true; auto.
        apply used_in_cmd_fun_spec.

    destruct J3 as [J3 J4]. clear J2.
    destruct (eq_atom_dec id0 (getCmdLoc a)); subst.
      inv J1. clear IHcs J3.
      remember (used_in_cmd pid a) as R.
      destruct R.
        destruct a; auto.
          apply andb_true_iff in J4.
          destruct J4; auto.
        destruct a; auto.
          simpl in *.
          symmetry in HeqR.
          apply orb_false_iff in HeqR.
           destruct HeqR.
           apply unused_in_value__neg_valueEqB; auto.

      clear J4.
      eapply IHcs in J3; eauto.
Qed.

Lemma neg_valueEqB__unused_in_value: forall pid v,
  negb (valueEqB v (value_id pid)) ->
  used_in_value pid v = false.
Proof.
  intros.
  unfold valueEqB in H.
  destruct v as [i0|]; auto.
  destruct (value_dec (value_id i0) (value_id pid)); simpl in *.
    congruence.

    destruct (id_dec i0 pid); subst; auto.
      congruence.
Qed.

Lemma unused_in_list_value__unused_in_value: forall pid v0 l0,
  used_in_list_value pid l0 = false ->
  valueInListValue v0 l0 ->
  used_in_value pid v0 = false.
Proof.
  induction l0; simpl; intros.
    inv H0.

    simpl_prod.
    apply orb_false_iff in H.
    destruct H as [J1 J2].
    inv H0; auto.
Qed.

Lemma unused_in_params__used_in_value: forall pid v0 ps
  (H1: fold_left
         (fun (acc : bool) (p : typ * attributes * value) =>
          let '(_, v) := p in used_in_value pid v || acc) ps false = false)
  (H2 : valueInParams v0 ps),
  used_in_value pid v0 = false.
Proof.
  induction ps as [|[]]; simpl; intros.
    inv H2.

    assert (forall (a : bool) (b : typ * attributes * value),
      (let '(_, v1) := b in used_in_value pid v1 || a) = false -> a = false).
      intros. destruct b.
      apply orb_false_iff in H.
      destruct H; auto.
    apply fold_left_or_false in H1; auto.
    destruct H1 as [J1 J2]. clear H.
    apply orb_false_iff in J2.
    destruct J2.
    unfold valueInParams in *.
    simpl in H2.
    remember (split ps) as R.
    destruct R.
    simpl in H2.
    destruct H2 as [H2 | H2]; subst; auto.
Qed.

Lemma unused_in_phis__unused_in_phi': forall (pid: id) (ps: phinodes)
  (p0 : phinode) (J1 : InPhiNodesB p0 ps)
  (J2 : fold_left (fun (re : bool) (p : phinode) => re || used_in_phi pid p)
          ps false = false),
  used_in_phi pid p0 = false.
Proof.
  induction ps; simpl; intros.
    congruence.

    assert (fold_left (fun (re : bool) (p : phinode) => re || used_in_phi pid p)
              ps false = false /\ used_in_phi pid a = false) as J3.
      apply fold_left_or_false; auto.
        apply used_in_phi_fun_spec.

    destruct J3 as [J3 J4].
    apply orb_true_iff in J1.
    destruct J1 as [J1 | J1]; auto.
      apply phinodeEqB_inv in J1. subst. auto.
Qed.

Lemma unused_in_cmds__unused_in_cmd': forall (pid id0 : id) (cs : cmds)
  (c0 : cmd) (J1 : InCmdsB c0 cs)
  (J2 : fold_left
          (fun acc0 c =>
           if used_in_cmd pid c then
             match c with
             | insn_load _ _ _ _ => acc0
             | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) && acc0
             | _ => false
             end
           else acc0) cs true = true),
  match c0 with
  | insn_load _ _ _ _ => True
  | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid))
  | _ => used_in_cmd pid c0 = false
  end.
Proof.
  induction cs; simpl; intros.
    congruence.

    assert (
      fold_left
        (fun acc0 c =>
         if used_in_cmd pid c then
           match c with
           | insn_load _ _ _ _ => acc0
           | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) && acc0
           | _ => false
           end
         else acc0) cs true = true /\
      (if used_in_cmd pid a then
         match a with
         | insn_load _ _ _ _ => true
         | insn_store _ _ v _ _ => negb (valueEqB v (value_id pid)) && true
         | _ => false
         end
       else true) = true) as J3.
      apply fold_left_and_true; auto.
        apply used_in_cmd_fun_spec.

    destruct J3 as [J3 J4]. clear J2.
    apply orb_true_iff in J1.
    destruct J1 as [J1 | J1].
      clear IHcs J3.
      apply cmdEqB_inv in J1. subst.
      remember (used_in_cmd pid a) as R.
      destruct R.
        destruct a; auto.
          apply andb_true_iff in J4.
          destruct J4; auto.

        destruct a; auto.
          simpl in *.
          symmetry in HeqR.
          apply orb_false_iff in HeqR.
          destruct HeqR.
          apply unused_in_value__neg_valueEqB; auto.

      clear J4.
      eapply IHcs in J3; eauto.
Qed.

(*************************************************************)
(* remove lifetime intrinsics                                *)

Parameter is_llvm_lifetime : id -> bool.

Fixpoint remove_lifetime_from_cmds (cs:cmds) : cmds :=
match cs with
| nil => nil
| (insn_cast _ castop_bitcast _ _ _) as c1::
  (insn_call _ _ _ _ _ (value_const (const_gid _ fid)) _) as c2:: tl =>
    if is_llvm_lifetime fid then remove_lifetime_from_cmds tl
    else c1::c2::remove_lifetime_from_cmds tl
| hd::tl => hd::remove_lifetime_from_cmds tl
end.

Definition remove_lifetime_from_fdef (f:fdef) : fdef :=
let '(fdef_intro fh bs) := f in
  fdef_intro fh
       (List.map (fun b =>
                  let '(l0, stmts_intro ps0 cs tmn0) := b in
                  (l0, stmts_intro ps0 (remove_lifetime_from_cmds cs) tmn0)) bs).

Definition remove_lifetime_from_module := 
  transf_from_module remove_lifetime_from_fdef.

(*********************************************************************)
(* remove allocas for dbg intrinsics, which prevents from identifying 
   promotable allocas. *)

Parameter is_llvm_dbg_declare : id -> bool.

Definition remove_dbg_declare (pid:id) (f:fdef) : fdef :=
  let uses := find_uses_in_fdef pid f in
  let re := List.fold_left
    (fun acc i =>
     match acc with
     | None => None
     | Some (bldst, ocid, orid) =>
         match i with 
         | insn_cmd (insn_load _ _ _ _) => Some (true, ocid, orid)
         | insn_cmd (insn_store _ _ v _ _) => 
             if valueEqB v (value_id pid) 
             then None else Some (true, ocid, orid)
         | insn_cmd (insn_cast cid castop_bitcast _ _ _) =>
             match ocid with
             | Some _ => 
                 (* not remove if used by multiple bitcast *)
                 None
             | None =>
                 match find_uses_in_fdef cid f with
                 | insn_cmd 
                     (insn_call rid _ _ _ _ (value_const (const_gid _ fid)) _)
                     ::nil =>
                     if is_llvm_dbg_declare fid then 
                       Some (bldst, Some cid, Some rid)
                     else None
                 | _ => None
                 end
              end
         | _ => None
         end
     end)
    uses (Some (false, None, None)) in
  match re with
  | Some (true, Some cid, Some rid) => 
      (* if pid is used by ld/st and a simple dbg *)
      remove_fdef cid (remove_fdef rid f)
  | _ => f
  end.
 
Fixpoint remove_dbg_declares (f:fdef) (cs:cmds) : fdef :=
match cs with
| nil => f
| insn_alloca pid _ _ _ :: cs' =>
    remove_dbg_declares (remove_dbg_declare pid f) cs'
| _ :: cs' => remove_dbg_declares f cs'
end.

Definition remove_dbg_declares_from_fdef (f:fdef) : fdef :=
match getEntryBlock f with
| Some (_, stmts_intro _ cs _) => remove_dbg_declares f cs
| _ => f
end.

Definition remove_dbg_declares_from_module := 
  transf_from_module remove_dbg_declares_from_fdef.

(*********************************************************************)
(* fix temporary names when pp-printing                              *)

Variable TNAME:Type.
Parameter init_expected_name : unit -> TNAME.
Parameter check_vname : id -> TNAME -> option (id * TNAME).
Parameter check_bname : l -> TNAME -> option (l * TNAME).

Definition fix_temporary_block (f:fdef) (b:block) (eid:TNAME) : 
  option (fdef * TNAME) :=
  let '(l0, stmts_intro ps cs _) := b in
  match check_bname l0 eid with
  | Some (l0', eid5) =>
    let st :=
    fold_left
      (fun st p =>
       match st with
       | Some (f0, eid0) =>
           let pid := getPhiNodeID p in
           match check_vname pid eid0 with
           | None => None
           | Some (pid', eid') =>
               if (id_dec pid pid') then Some (f0, eid')
               else Some (rename_fdef pid pid' f0, eid')
           end
       | _ => None
       end) 
       ps (Some ((renamel_fdef l0 l0' f), eid5)) in
    fold_left
      (fun st c =>
       match st with
       | Some (f0, eid0) =>
           match getCmdID c with
           | None => Some (f0, eid0)
           | Some cid =>
              match check_vname cid eid0 with
              | None => None
              | Some (cid', eid') =>
                  if (id_dec cid cid') then Some (f0, eid')
                  else Some (rename_fdef cid cid' f0, eid')
              end
           end
       | _ => None
       end) cs st
  | None => None
  end.

Definition fix_temporary_fdef (f:fdef) : option fdef :=
  let '(fdef_intro (fheader_intro _ _ _ ars _) bs) := f in
  (* arguments can also contain temporaries, scan args first *)
  let st0 := fold_left 
    (fun st ar =>
     match st with
     | None => None
     | Some eid0 =>
        let '(_, aid) := ar in
        match check_vname aid eid0 with
        | None => None
        | Some (_, eid1) => Some eid1
        end
     end) ars (Some (init_expected_name tt)) in
  match st0 with
  | None => None
  | Some eid =>
    match fold_left 
      (fun st b => 
       match st with
       | Some (f0, eid0) =>
           match fix_temporary_block f0 b eid0 with
           | Some (f1, eid1) => Some (f1, eid1)
           | None => None
           end
       | _ => None
       end) bs (Some (f, eid)) with
    | Some (f', _) => Some f'
    | None => None
    end
  end.

Definition fix_temporary_module := 
  transf_from_module (fun f => 
                      match fix_temporary_fdef f with
		      | Some f' => f'
                      | _ => f
                      end).
