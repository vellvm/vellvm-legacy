Require Import vellvm.
Require Import Lattice.
Require Import Maps.
Require Import dtree.

Definition subst_value (id':id) (v':value) (v:value) : value :=
match v with
| value_id id1 => if id_dec id1 id' then v' else v
| _ => v
end.

Notation "v {[ v' // id' ]}" :=
  ( subst_value id' v' v ) (at level 42, no associativity).

Fixpoint subst_list_value (id':id) (v':value) (vl:list_sz_value)
  : list_sz_value :=
match vl with
| Nil_list_sz_value => Nil_list_sz_value
| Cons_list_sz_value sz0 v0 tl =>
   Cons_list_sz_value sz0 (v0{[v'//id']}) (subst_list_value id' v' tl)
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

Fixpoint subst_list_value_l (id':id) (v':value ) (l0:list_value_l)
  : list_value_l :=
match l0 with
| Nil_list_value_l => Nil_list_value_l
| Cons_list_value_l v0 l0 tl =>
   Cons_list_value_l (v0{[v'//id']}) l0 (subst_list_value_l id' v' tl)
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

Definition subst_block (id':id) (v':value) (b:block) : block :=
match b with
| block_intro l0 ps0 cs0 tmn0 =>
  block_intro l0 (List.map (subst_phi id' v') ps0)
    (List.map (subst_cmd id' v') cs0) (subst_tmn id' v' tmn0)
end.

Definition subst_fdef (id':id) (v':value) (f:fdef) : fdef :=
match f with
| fdef_intro fh bs => fdef_intro fh (List.map (subst_block id' v') bs)
end.

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

Definition remove_phinodes (id':id) (ps:phinodes) : phinodes :=
  (List.filter (fun p => negb (id_dec (getPhiNodeID p) id')) ps).

Definition remove_cmds (id':id) (cs:cmds) : cmds :=
  (List.filter (fun c => negb (id_dec (getCmdLoc c) id')) cs).

Definition remove_block (id':id) (b:block) : block :=
match b with
| block_intro l0 ps0 cs0 tmn0 =>
  block_intro l0 (remove_phinodes id' ps0) (remove_cmds id' cs0) tmn0
end.

Definition remove_fdef (id':id) (f:fdef) : fdef :=
match f with
| fdef_intro fh bs => fdef_intro fh (List.map (remove_block id') bs)
end.

Definition used_in_value (id0:id) (v:value) : bool :=
match v with
| value_id id1 => id_dec id1 id0
| _ => false
end.

Fixpoint used_in_list_value (id0:id) (vl:list_sz_value) : bool :=
match vl with
| Nil_list_sz_value => false
| Cons_list_sz_value _ v0 tl =>
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

Fixpoint used_in_list_value_l (id':id) (l0:list_value_l) : bool :=
match l0 with
| Nil_list_value_l => false
| Cons_list_value_l v0 _ tl =>
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
| block_intro _ ps0 cs0 tmn0 =>
  (List.fold_left (fun re p => re || used_in_phi id' p) ps0 false) ||
  (List.fold_left (fun re c => re || used_in_cmd id' c) cs0 false) ||
  (used_in_tmn id' tmn0)
end.

Definition used_in_fdef (id':id) (f:fdef) : bool :=
match f with
| fdef_intro _ bs =>
  List.fold_left (fun re b => re || used_in_block id' b) bs false
end.

Definition find_uses_in_block (id':id) (b:block) : list insn :=
let '(block_intro _ ps cs tmn) := b in
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

Definition store_in_cmd (id':id) (c:cmd) : bool :=
match c with
| insn_store _ _ _ ptr _ => used_in_value id' ptr
| _ => false
end.

Definition store_in_cmds (id':id) (cs:cmds) : bool :=
(List.fold_left (fun re c => re || store_in_cmd id' c) cs false).

Definition insert_cmds (n:nat) (c:cmd) (cs : cmds) : cmds :=
firstn n cs ++ c :: skipn n cs.

(* insert c at the n-th position in block l1 *)
Definition insert_block (l1:l) (n:nat) (c:cmd) (b:block) : block :=
match b with
| block_intro l0 ps0 cs0 tmn0 =>
    block_intro l0 ps0 (if (l_dec l1 l0)
                        then insert_cmds n c cs0
                        else cs0) tmn0
end.

Definition insert_fdef (l1:l) (n:nat) (c:cmd) (f:fdef) : fdef :=
let '(fdef_intro fh bs) := f in
fdef_intro fh (List.map (insert_block l1 n c) bs).

Definition rename_id (id1:id) (id2:id) (id0:id) : id :=
if id_dec id0 id1 then id2 else id0.

Definition rename_value (id1:id) (id2:id) (v:value) : value :=
match v with
| value_id id0 => value_id (rename_id id1 id2 id0)
| _ => v
end.

Fixpoint rename_list_value (id1 id2:id) (vl:list_sz_value) : list_sz_value :=
match vl with
| Nil_list_sz_value => Nil_list_sz_value
| Cons_list_sz_value sz0 v0 tl =>
    Cons_list_sz_value sz0 (rename_value id1 id2 v0)
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

Fixpoint rename_list_value_l (id1:id) (id2:id) (l0:list_value_l)
  : list_value_l :=
match l0 with
| Nil_list_value_l => Nil_list_value_l
| Cons_list_value_l v0 l0 tl =>
   Cons_list_value_l (rename_value id1 id2 v0) l0
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

Definition rename_block (id1:id) (id2:id) (b:block) : block :=
match b with
| block_intro l0 ps0 cs0 tmn0 =>
  block_intro l0 (List.map (rename_phi id1 id2) ps0)
    (List.map (rename_cmd id1 id2) cs0) (rename_tmn id1 id2 tmn0)
end.

Definition rename_fheader (id1 id2:id) (fh:fheader) : fheader :=
let '(fheader_intro fr t0 fid la va):=fh in
fheader_intro fr t0 fid
  (List.map (fun a => let '(p,id0):=a in (p,rename_id id1 id2 id0)) la) va.

Definition rename_fdef (id1:id) (id2:id) (f:fdef) : fdef :=
match f with
| fdef_intro fh bs =>
    fdef_intro (rename_fheader id1 id2 fh) (List.map (rename_block id1 id2) bs)
end.

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
Parameter print_dominators : forall bd, AMap.t (Dominators.t bd) -> bool.
Parameter print_dtree : DTree -> bool.

Variable TNAME: Type.
Parameter init_expected_name : unit -> TNAME.
Parameter check_bname : l -> TNAME -> option (l * TNAME).
Parameter check_vname : id -> TNAME -> option (id * TNAME).

Fixpoint renamel_list_value_l (l1 l2:l) (l0:list_value_l) : list_value_l :=
match l0 with
| Nil_list_value_l => Nil_list_value_l
| Cons_list_value_l v0 l0 tl =>
   Cons_list_value_l v0 (rename_id l1 l2 l0) (renamel_list_value_l l1 l2 tl)
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
| block_intro l0 ps0 cs0 tmn0 =>
  block_intro (rename_id l1 l2 l0) (List.map (renamel_phi l1 l2) ps0) cs0 
    (renamel_tmn l1 l2 tmn0)
end.

Definition renamel_fdef (l1 l2:l) (f:fdef) : fdef :=
match f with
| fdef_intro fh bs =>
    fdef_intro fh (List.map (renamel_block l1 l2) bs)
end.

Definition fix_temporary_block (f:fdef) (b:block) (eid:TNAME)
  : option (fdef * TNAME) :=
let '(block_intro l0 ps cs _) := b in
match check_bname l0 eid with
| Some (l0', eid5) =>
  let st :=
  fold_left
    (fun st p =>
     match st with
     | Some (f0, eid0) =>
         let 'pid := getPhiNodeID p in
         match check_vname pid eid0 with
         | None => None
         | Some (pid', eid') =>
             if (id_dec pid pid') then Some (f0, eid')
             else Some (rename_fdef pid pid' f0, eid')
         end
     | _ => None
     end) ps (Some ((renamel_fdef l0 l0' f), eid5)) in
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

Definition getFdefLocs fdef : ids :=
match fdef with
| fdef_intro (fheader_intro _ _ _ la _) bs => getArgsIDs la ++ getBlocksLocs bs
end.

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
Admitted. (* infra *)

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

    unfold valueInListValue in H0.
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
  blockInFdefB (block_intro l3 ps1 cs tmn1) F1 = true ->
  valueInCmdOperands v c -> In c cs ->
  used_in_value id0 v = false.
Proof.
  destruct F1. simpl. intros.
  eapply used_in_blocks__used_in_block in H0; eauto.
  binvf H0 as J3 J4. binvf J3 as J1 J2.
  eapply used_in_cmds__used_in_cmd in J2; eauto.
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
  blockInFdefB (block_intro l3 ps1 cs tmn1) F1 = true ->
  valueInTmnOperands v tmn1 ->
  used_in_value id0 v = false.
Proof.
  destruct F1. simpl. intros.
  eapply used_in_blocks__used_in_block in H0; eauto.
  binvf H0 as J3 J4. binvf J3 as J1 J2.
  eapply used_in_tmn__used_in_value in H1; eauto.
Qed.

Lemma used_in_fdef__used_in_block : forall id0 b F1,
  used_in_fdef id0 F1 = false ->
  blockInFdefB b F1 = true ->
  used_in_block id0 b = false.
Proof.
  destruct F1. simpl. intros.
  eapply used_in_blocks__used_in_block in H0; eauto.
Qed.

Lemma fdef_sim__lookupAL_genLabel2Block_block : forall id0 l0 bs b b',
  lookupAL _ (genLabel2Block_blocks bs) l0 = Some b ->
  lookupAL _ (genLabel2Block_blocks (List.map (remove_block id0) bs)) l0
    = Some b' ->
  remove_block id0 b = b'.
Proof.
  induction bs as [|a ?]; simpl; intros.
    congruence.

    destruct a as [l1 ? ? ?]. simpl in *.
    destruct (l0 == l1); subst; eauto.
      inv H. inv H0. auto.
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
