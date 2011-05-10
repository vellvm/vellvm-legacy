Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa".
Add LoadPath "../ssa/compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Add LoadPath "../TV".
Require Import ssa_def.
Require Import ssa_lib.
Require Import trace.
Require Import Memory.
Require Import genericvalues.
Require Import assoclist.
Require Import Integers.
Require Import Values.
Require Import Coqlib.
Require Import monad.
Require Import Metatheory.
Require Import Znumtheory.
Require Import sb_def.

Module SBpass.

Export LLVMsyntax.
Export LLVMgv.

Definition rmap := list (id*(id*id)).

Definition getFdefIDs fdef : ids :=
match fdef with
| fdef_intro (fheader_intro _ _ la) bs => 
  let '(_, ids0) := List.split la in
  ids0 ++ getBlocksIDs bs 
end.

Definition gen_metadata_id (ex_ids:ids) (rm:rmap) (id0:id) 
  : id * id * ids * rmap :=
let '(exist b _) := AtomImpl.atom_fresh_for_list ex_ids in
let '(exist e _) := AtomImpl.atom_fresh_for_list (b::ex_ids) in
(b, e, b::e::ex_ids, (id0,(b,e))::rm).

Fixpoint gen_metedata_cmds (ex_ids:ids) (rm:rmap) (cs:cmds) : option(ids*rmap) :=
match cs with
| nil => Some (ex_ids,rm)
| c::cs' => 
   do t <- getCmdTyp c;
   if isPointerTypB t then
     let id0 := getCmdID c in
     let '(_,_,ex_ids',rm') := gen_metadata_id ex_ids rm id0 in
     gen_metedata_cmds ex_ids' rm' cs'
   else gen_metedata_cmds ex_ids rm cs'
end.

Fixpoint gen_metedata_phinodes (ex_ids:ids) (rm:rmap) (ps:phinodes) : ids*rmap :=
match ps with
| nil => (ex_ids,rm)
| p::ps' => 
   let t := getPhiNodeTyp p in
   if isPointerTypB t then
     let id0 := getPhiNodeID p in
     let '(_,_,ex_ids',rm') := gen_metadata_id ex_ids rm id0 in
     gen_metedata_phinodes ex_ids' rm' ps'
   else gen_metedata_phinodes ex_ids rm ps'
end.

Definition gen_metedata_block (ex_ids:ids) (rm:rmap) (b:block) : option(ids*rmap)
  :=
let '(block_intro _ ps cs _) := b in
let '(ex_ids', rm') := gen_metedata_phinodes ex_ids rm ps in
gen_metedata_cmds ex_ids' rm' cs.

Fixpoint gen_metedata_blocks (ex_ids:ids) (rm:rmap) (bs:blocks) 
  : option(ids*rmap) :=
match bs with
| nil => Some (ex_ids,rm)
| b::bs' => 
    match gen_metedata_block ex_ids rm b with
    | Some (ex_ids',rm') => gen_metedata_blocks ex_ids' rm' bs'
    | None => None
    end
end.

Fixpoint gen_metedata_args (ex_ids:ids) (rm:rmap) (la:args) : ids*rmap :=
match la with
| nil => (ex_ids,rm)
| (t,id0)::la' => 
   if isPointerTypB t then
     let '(_,_,ex_ids',rm') := gen_metadata_id ex_ids rm id0 in
     gen_metedata_args ex_ids' rm' la'
   else gen_metedata_args ex_ids rm la'
end.

Definition gen_metedata_fdef (ex_ids:ids) (rm:rmap) (f:fdef) : option(ids*rmap)
  :=
let '(fdef_intro (fheader_intro _ _ la) bs) := f in
let '(ex_ids', rm') := gen_metedata_args ex_ids rm la in
gen_metedata_blocks ex_ids' rm' bs.

Definition mk_tmp (ex_ids:ids) : id * ids :=
let '(exist tmp _) := AtomImpl.atom_fresh_for_list ex_ids in
(tmp, tmp::ex_ids).

Definition i8 := typ_int Size.Eight.
Definition p8 := typ_pointer i8.
Definition pp8 := typ_pointer p8.
Definition c1 := 
  Cons_list_value 
    (value_const 
      (const_int Size.ThirtyTwo 
        (INTEGER.of_Z 32%Z 1%Z false))) 
    Nil_list_value.

Definition get_reg_metadata (rm:rmap) (v:value) : option (value * value) :=
  match v with
  | value_id pid => 
      match lookupAL _ rm pid with
      | Some (bid, eid) => Some (value_id bid, value_id eid)
      | None => None
      end
  | value_const c => 
      match SoftBound.get_const_metadata c with
      | Some (bc, ec) => Some (value_const bc, value_const ec)
      | None => None
      end
  end.

Parameter assert_mptr_fid : id.
Parameter fake_id : id.
Parameter get_mmetadata_fid : id.
Parameter set_mmetadata_fid : id.

Definition assert_mptr_fn : value :=
  value_const
    (const_gid 
      (typ_function typ_void 
        (Cons_list_typ p8 (Cons_list_typ p8 (Cons_list_typ p8 Nil_list_typ))))
      assert_mptr_fid).

Definition get_mmetadata_fn : value :=
  value_const
    (const_gid 
      (typ_function typ_void 
        (Cons_list_typ p8 
        (Cons_list_typ pp8 
        (Cons_list_typ pp8 Nil_list_typ))))
      get_mmetadata_fid).

Definition set_mmetadata_fn : value :=
  value_const
    (const_gid 
      (typ_function typ_void 
        (Cons_list_typ p8 
        (Cons_list_typ p8 
        (Cons_list_typ p8 Nil_list_typ))))
      set_mmetadata_fid).

Definition prop_metadata (ex_ids tmps:ids) rm c v1 id0 :=
  match (get_reg_metadata rm v1, lookupAL _ rm id0) with
  | (Some (bv, ev), Some (bid0, eid0)) =>
      Some (ex_ids, tmps,
        c::
        insn_cast bid0 castop_bitcast p8 bv p8:: 
        insn_cast eid0 castop_bitcast p8 ev p8:: 
        nil)
  | _ => None
  end.

Definition trans_cmd (ex_ids tmps:ids) (addrb addre:id) (rm:rmap) (c:cmd) 
  : option (ids*ids*cmds) :=
match c with 
| insn_malloc id0 t1 v1 al1 | insn_alloca id0 t1 v1 al1 =>
    match lookupAL _ rm id0 with
    | Some (bid, eid) =>
      let '(tmp,ex_ids') := mk_tmp ex_ids in
      Some (ex_ids', tmp::tmps,
       c::
       insn_cast bid castop_bitcast (typ_pointer t1) (value_id id0) p8:: 
       insn_gep tmp false (typ_pointer t1) (value_id id0) c1 :: 
       insn_cast eid castop_bitcast (typ_pointer t1) (value_id tmp) p8:: 
       nil)
    | _ => None
    end

| insn_load id0 t2 v2 align => 
    match get_reg_metadata rm v2 with
    | Some (bv, ev) =>
      let '(ptmp,ex_ids) := mk_tmp ex_ids in
      let '(btmp,ex_ids) := mk_tmp ex_ids in
      let '(etmp,ex_ids) := mk_tmp ex_ids in
      let optcs := 
        if isPointerTypB t2 then
          match lookupAL _ rm id0 with
          | Some (bid0, eid0) =>
              Some
                (insn_call fake_id true false typ_void get_mmetadata_fn 
                  ((p8,(value_id ptmp))::
                   (p8,(value_id addrb))::
                   (p8,(value_id addre))::nil)::
                 insn_load bid0 p8 (value_id addrb) Align.One::
                 insn_load eid0 p8 (value_id addre) Align.One::   
                 nil)
          | None => None
          end
        else Some nil in
      match optcs with
      | None => None
      | Some cs =>
        Some (ex_ids, ptmp::btmp::etmp::tmps,
         insn_cast ptmp castop_bitcast (typ_pointer t2) v2 p8:: 
         insn_cast btmp castop_bitcast (typ_pointer t2) bv p8:: 
         insn_cast etmp castop_bitcast (typ_pointer t2) ev p8:: 
         insn_call fake_id true false typ_void assert_mptr_fn 
           ((p8,(value_id ptmp))::
            (p8,(value_id btmp))::
            (p8,(value_id etmp))::nil)::
         c::
         cs)
      end
    | None => None
    end

| insn_store id0 t0 v1 v2 align =>
    match get_reg_metadata rm v2 with
    | Some (bv, ev) =>
      let '(ptmp,ex_ids) := mk_tmp ex_ids in
      let '(btmp,ex_ids) := mk_tmp ex_ids in
      let '(etmp,ex_ids) := mk_tmp ex_ids in
      let optcs := 
        if isPointerTypB t0 then
          match lookupAL _ rm id0 with
          | Some (bid0, eid0) =>
              Some
                (insn_call fake_id true false typ_void set_mmetadata_fn 
                  ((p8,(value_id ptmp))::
                   (p8,(value_id bid0))::
                   (p8,(value_id eid0))::nil)::
                 nil)
          | None => None
          end
        else Some nil in
      match optcs with
      | None => None
      | Some cs =>
        Some (ex_ids, ptmp::btmp::etmp::tmps,
         insn_cast ptmp castop_bitcast (typ_pointer t0) v2 p8:: 
         insn_cast btmp castop_bitcast (typ_pointer t0) bv p8:: 
         insn_cast etmp castop_bitcast (typ_pointer t0) ev p8:: 
         insn_call fake_id true false typ_void assert_mptr_fn 
           ((p8,(value_id ptmp))::
            (p8,(value_id btmp))::
            (p8,(value_id etmp))::nil)::
         c::
         cs)
      end
    | None => None
    end

| insn_gep id0 inbounds0 t1 v1 lv2 => prop_metadata ex_ids tmps rm c v1 id0

| insn_cast id0 op0 t1 v1 t2 => 
    match op0 with
    | castop_bitcast =>
        if isPointerTypB t1 then
          prop_metadata ex_ids tmps rm c v1 id0
        else Some (ex_ids, tmps, [c])
    | castop_inttoptr =>
        match lookupAL _ rm id0 with
        | Some (bid0, eid0) =>
            Some (ex_ids, tmps,
              c::
              insn_cast bid0 castop_bitcast p8 (value_const (const_null p8)) p8::
              insn_cast eid0 castop_bitcast p8 (value_const (const_null p8)) p8::
              nil)
        | _ => None
        end
    | _ => Some (ex_ids, tmps, [c])
    end

| insn_select id0 v0 t0 v1 v2 =>
    if isPointerTypB t0 then
      match (get_reg_metadata rm v1, get_reg_metadata rm v2, 
             lookupAL _ rm id0) with
      | (Some (bv1, ev1), Some (bv2, ev2), Some (bid0, eid0)) =>
          Some (ex_ids, tmps,
            c::
            insn_select bid0 v0 p8 bv1 bv2:: 
            insn_select eid0 v0 p8 ev1 ev2:: 
            nil)
      | _ => None
      end
    else Some (ex_ids, tmps, [c])

| _ => Some (ex_ids, tmps, [c])
end.

Fixpoint trans_cmds (ex_ids tmps:ids) (addrb addre:id) (rm:rmap) (cs:cmds) 
  : option (ids*ids*cmds) :=
match cs with
| nil => Some (ex_ids, tmps, nil)
| c::cs' =>
    match (trans_cmd ex_ids tmps addrb addre rm c) with
    | Some (ex_ids1, tmps1, cs1) =>
        match (trans_cmds ex_ids1 tmps1 addrb addre rm cs') with
        | Some (ex_ids2, tmps2, cs2) => Some (ex_ids2, tmps2, cs1++cs2)
        | _ => None
        end
    | _ => None
    end
end.

Fixpoint get_metadata_from_list_value_l (rm:rmap) (vls:list_value_l) 
  (baccum eaccum : list_value_l): option (list_value_l * list_value_l) :=
match vls with
| Nil_list_value_l => Some (baccum, eaccum)
| Cons_list_value_l v0 l0 vls' => 
    match get_reg_metadata rm v0 with
    | Some (bv, ev) =>
        get_metadata_from_list_value_l rm vls' 
          (Cons_list_value_l bv l0 baccum) (Cons_list_value_l ev l0 eaccum)
    | _ => None
    end
end.

Fixpoint trans_phinodes (rm:rmap) (ps:phinodes) : option phinodes :=
match ps with
| nil => Some nil
| (insn_phi id0 t0 vls0 as p)::ps' =>
    match trans_phinodes rm ps' with
    | None => None
    | Some ps2 =>
        if isPointerTypB t0 then
          match (get_metadata_from_list_value_l rm vls0 Nil_list_value_l 
                 Nil_list_value_l,
                lookupAL _ rm id0) with
          | (Some (bvls0, evls0), Some (bid0, eid0)) => 
              Some (p::insn_phi bid0 p8 bvls0::insn_phi eid0 p8 evls0::ps2)
          | _ => None
          end
        else Some (p::ps2)
    end
end.

Definition trans_block (ex_ids tmps:ids) (addrb addre:id) (rm:rmap) (b:block) 
  : option (ids*ids*block) :=
let '(block_intro l1 ps1 cs1 tmn1) := b in
match trans_phinodes rm ps1 with
| None => None
| Some ps2 => 
    match trans_cmds ex_ids tmps addrb addre rm cs1 with
    | Some (ex_ids',tmps',cs2) => 
        Some (ex_ids',tmps',block_intro l1 ps2 cs2 tmn1)
    | None => None
    end
end.

Fixpoint trans_blocks (ex_ids tmps:ids) (addrb addre:id) (rm:rmap) (bs:blocks) 
  : option (ids*ids*blocks) :=
match bs with
| nil => Some (ex_ids, tmps, nil)
| b::bs' =>
    match (trans_block ex_ids tmps addrb addre rm b) with
    | Some (ex_ids1, tmps1, b1) =>
        match (trans_blocks ex_ids1 tmps1 addrb addre rm bs') with
        | Some (ex_ids2, tmps2, bs2) => Some (ex_ids2, tmps2, b1::bs2)
        | _ => None
        end
    | _ => None
    end
end.

Fixpoint trans_args (rm:rmap) (la:args) : option args :=
match la with
| nil => Some nil
| (t0,id0) as a::la' =>
    match trans_args rm la' with
    | None => None
    | Some la2 =>
      if isPointerTypB t0 then
        match (lookupAL _ rm id0) with
        | Some (bid0, eid0) => 
            Some ((p8,bid0)::(p8,id0)::la2)
        | _ => None
        end
      else Some la2
    end
end.

Definition trans_fdef (f:fdef) : option (rmap*ids*fdef) :=
let '(fdef_intro (fheader_intro t fid la) bs) := f in
let ex_ids := getFdefIDs f in
match gen_metedata_fdef ex_ids nil f with
| Some (ex_ids,rm) =>
    match (trans_args rm la) with
    | Some la' =>
        let '(addrb,ex_ids) := mk_tmp ex_ids in
        let '(addre,ex_ids) := mk_tmp ex_ids in
        match (trans_blocks ex_ids (addrb::addre::nil) addrb addre rm bs) with
        | Some (ex_ids, tmps, bs') => 
            Some (rm, tmps, fdef_intro (fheader_intro t fid (la++la')) bs')
        | _ => None
        end
    | _ => None
    end
| None => None
end.

Fixpoint trans_product (p:product) : option product :=
match p with
| product_fdef f =>
    match trans_fdef f with
    | None => None
    | Some (_,_,f') => Some (product_fdef f')
    end
| _ => Some p
end.

Fixpoint trans_products (ps:products) : option products :=
match ps with
| nil => Some nil
| p::ps' =>
    match (trans_product p) with
    | Some p1 =>
        match (trans_products ps') with
        | Some ps2 => Some (p1::ps2)
        | _ => None
        end
    | _ => None
    end
end.

Definition trans_module (m:module) : option module :=
let '(module_intro los nts ps) := m in
do ps' <- trans_products ps;
ret (module_intro los nts ps').

Fixpoint trans_system (ms:system) : option system :=
match ms with
| nil => Some nil
| m::ms' =>
    match (trans_module m) with
    | Some m1 =>
        match (trans_system ms') with
        | Some ms2 => Some (m1::ms2)
        | _ => None
        end
    | _ => None
    end
end.

End SBpass.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)
