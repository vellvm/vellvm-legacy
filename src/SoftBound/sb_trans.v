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
Require Import symexe_def.
Require Import sb_tactic.
Require Import sub_tv.
Require Import sb_pp.

Module SBpass.

Export LLVMsyntax.
Export LLVMgv.

Definition simpl_typ (nts:namedts) (t:typ) : option typ :=
do ut <- typ2utyp nts t; ret (utyp2typ ut).

Definition getGEPTyp (nts:namedts) (idxs : list_value) (t : typ) : option typ :=
match idxs with
| Nil_list_value => None
| Cons_list_value idx idxs' =>
    do t <- simpl_typ nts t;
    (* The input t is already an element of a pointer typ *)
    do t' <- getSubTypFromValueIdxs idxs' t;
    ret (typ_pointer t')
end.

Definition getCmdTyp (nts:namedts) (i:cmd) : option typ :=
match i with
| insn_bop _ _ sz _ _ => Some (typ_int sz)
| insn_fbop _ _ ft _ _ => Some (typ_floatpoint ft)
(*
| insn_extractelement _ typ _ _ => getElementTyp typ
| insn_insertelement _ typ _ _ _ _ => typ *)
| insn_extractvalue _ typ _ idxs => 
    do t <- simpl_typ nts typ;
    getSubTypFromConstIdxs idxs t
| insn_insertvalue _ typ _ _ _ _ => Some typ
| insn_malloc _ typ _ _ => Some (typ_pointer typ)
| insn_free _ typ _ => Some typ_void
| insn_alloca _ typ _ _ => Some (typ_pointer typ)
| insn_load _ typ _ _ => Some typ
| insn_store _ _ _ _ _ => Some typ_void
| insn_gep _ _ typ _ idxs => getGEPTyp nts idxs typ
| insn_trunc _ _ _ _ typ => Some typ
| insn_ext _ _ _ _ typ2 => Some typ2
| insn_cast _ _ _ _ typ => Some typ
| insn_icmp _ _ _ _ _ => Some (typ_int Size.One)
| insn_fcmp _ _ _ _ _ => Some (typ_int Size.One)
| insn_select _ _ typ _ _ => Some typ
| insn_call _ true _ typ _ _ => Some typ_void
| insn_call _ false _ typ _ _ => Some typ
end.

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

Fixpoint gen_metedata_cmds nts (ex_ids:ids) (rm:rmap) (cs:cmds) 
  : option(ids*rmap) :=
match cs with
| nil => Some (ex_ids,rm)
| c::cs' => 
   do t <- getCmdTyp nts c;
   if isPointerTypB t then
     let id0 := getCmdID c in
     let '(_,_,ex_ids',rm') := gen_metadata_id ex_ids rm id0 in
     gen_metedata_cmds nts ex_ids' rm' cs'
   else gen_metedata_cmds nts ex_ids rm cs'
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

Definition gen_metedata_block nts (ex_ids:ids) (rm:rmap) (b:block) 
  : option(ids*rmap) :=
let '(block_intro _ ps cs _) := b in
let '(ex_ids', rm') := gen_metedata_phinodes ex_ids rm ps in
gen_metedata_cmds nts ex_ids' rm' cs.

Fixpoint gen_metedata_blocks nts (ex_ids:ids) (rm:rmap) (bs:blocks) 
  : option(ids*rmap) :=
match bs with
| nil => Some (ex_ids,rm)
| b::bs' => 
    match gen_metedata_block nts ex_ids rm b with
    | Some (ex_ids',rm') => gen_metedata_blocks nts ex_ids' rm' bs'
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

Definition gen_metedata_fdef nts (ex_ids:ids) (rm:rmap) (f:fdef) 
  : option(ids*rmap) :=
let '(fdef_intro (fheader_intro _ _ la) bs) := f in
let '(ex_ids', rm') := gen_metedata_args ex_ids rm la in
gen_metedata_blocks nts ex_ids' rm' bs.

Definition mk_tmp (ex_ids:ids) : id * ids :=
let '(exist tmp _) := AtomImpl.atom_fresh_for_list ex_ids in
(tmp, tmp::ex_ids).

Definition i8 := typ_int Size.Eight.
Definition i32 := typ_int Size.ThirtyTwo.
Definition p8 := typ_pointer i8.
Definition pp8 := typ_pointer p8.
Definition p32 := typ_pointer i32.
Definition int1 := const_int Size.ThirtyTwo (INTEGER.of_Z 32%Z 1%Z false).
Definition vint1 := value_const int1.
Definition c1 := Cons_list_value vint1 Nil_list_value.
Definition vnullp8 := value_const (const_null p8).
Definition vnullp32 := value_const (const_null p32).

Definition get_reg_metadata (rm:rmap) (v:value) : option (typ * value * value) :=
  match v with
  | value_id pid => 
      match lookupAL _ rm pid with
      | Some (bid, eid) => Some (p8, value_id bid, value_id eid)
      | None => None
      end
  | value_const c => 
      match (SoftBound.get_const_metadata c, Constant.getTyp c) with
      | (Some (bc, ec), Some t) => Some (t, value_const bc, value_const ec)
      | (None, Some t) => Some (t, value_const (const_null t), 
                                   value_const (const_null t))
      | _ => None
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
        (Cons_list_typ p8 
        (Cons_list_typ p8 
        (Cons_list_typ p8
        (Cons_list_typ i32
        (Cons_list_typ i32 Nil_list_typ))))))
      assert_mptr_fid).

Definition get_mmetadata_fn : value :=
  value_const
    (const_gid 
      (typ_function typ_void 
        (Cons_list_typ p8 
        (Cons_list_typ pp8 
        (Cons_list_typ pp8
        (Cons_list_typ p8
        (Cons_list_typ i32
        (Cons_list_typ p32 Nil_list_typ)))))))
      get_mmetadata_fid).

Definition set_mmetadata_fn : value :=
  value_const
    (const_gid 
      (typ_function typ_void 
        (Cons_list_typ p8 
        (Cons_list_typ p8 
        (Cons_list_typ p8
        (Cons_list_typ p8
        (Cons_list_typ i32
        (Cons_list_typ i32 Nil_list_typ)))))))
      set_mmetadata_fid).

Definition prop_metadata (ex_ids tmps:ids) (optaddrb optaddre: option id) rm c v1
  id0 :=
  match (get_reg_metadata rm v1, lookupAL _ rm id0) with
  | (Some (t, bv, ev), Some (bid0, eid0)) =>
      Some (ex_ids, tmps,
        c::
        insn_cast bid0 castop_bitcast t bv p8:: 
        insn_cast eid0 castop_bitcast t ev p8:: 
        nil, 
        optaddrb, optaddre)
  | _ => None
  end.

Fixpoint trans_params (ex_ids tmps:ids) (rm:rmap) (lp:params) 
  : option (ids*ids*cmds*params) :=
match lp with
| nil => Some (ex_ids, tmps, nil, nil)
| (t0,v0) as p::lp' =>
    match trans_params ex_ids tmps rm lp' with
    | None => None
    | Some (ex_ids',tmps',cs,lp2) =>
      if isPointerTypB t0 then
        match get_reg_metadata rm v0 with
        | Some (mt, bv0, ev0) =>
            let '(btmp,ex_ids') := mk_tmp ex_ids' in
            let '(etmp,ex_ids') := mk_tmp ex_ids' in
            Some (
               ex_ids',
               btmp::etmp::tmps',
               insn_cast btmp castop_bitcast mt bv0 p8:: 
               insn_cast etmp castop_bitcast mt ev0 p8:: 
               cs,
               (p8,value_id btmp)::(p8,value_id etmp)::lp2
             )
        | _ => None
        end
      else Some (ex_ids',tmps',cs,lp2)
    end
end.

Axiom isSysLib : id -> bool.

Definition type_size t :=
  value_const
    (const_castop 
      castop_ptrtoint 
      (const_gep false 
        (const_null t) 
        (Cons_list_const int1 Nil_list_const))
      (typ_int Size.ThirtyTwo)
    ).

Definition trans_cmd (ex_ids tmps:ids) (optaddrb optaddre:option id) (rm:rmap) 
  (c:cmd) : option (ids*ids*cmds*option id*option id) :=
match c with 
| insn_malloc id0 t1 v1 al1 | insn_alloca id0 t1 v1 al1 =>
    match lookupAL _ rm id0 with
    | Some (bid, eid) =>
      let '(tmp,ex_ids') := mk_tmp ex_ids in
      Some (ex_ids', tmp::tmps,
       c::
       insn_cast bid castop_bitcast (typ_pointer t1) (value_id id0) p8:: 
       insn_gep tmp false t1 (value_id id0) 
         (Cons_list_value v1 Nil_list_value) :: 
       insn_cast eid castop_bitcast (typ_pointer t1) (value_id tmp) p8:: 
       nil,
       optaddrb, optaddre)
    | _ => None
    end

| insn_load id0 t2 v2 align => 
    match get_reg_metadata rm v2 with
    | Some (mt, bv, ev) =>
      let '(ptmp,ex_ids) := mk_tmp ex_ids in
      let '(btmp,ex_ids) := mk_tmp ex_ids in
      let '(etmp,ex_ids) := mk_tmp ex_ids in
      let '(optcs, ex_ids, tmps, optaddrb, optaddre) := 
        if isPointerTypB t2 then
          match lookupAL _ rm id0 with
          | Some (bid0, eid0) =>
              match (optaddrb, optaddre) with
              | (Some addrb, Some addre) =>
                   (Some
                     (insn_call fake_id true false typ_void get_mmetadata_fn 
                       ((p8,(value_id ptmp))::
                        (pp8,(value_id addrb))::
                        (pp8,(value_id addre))::
                        (p8,vnullp8)::
                        (i32,vint1)::
                        (p32,vnullp32)::
                        nil)::
                      insn_load bid0 p8 (value_id addrb) Align.Zero::
                      insn_load eid0 p8 (value_id addre) Align.Zero::   
                      nil), ex_ids, tmps, Some addrb, Some addre)
              | (None, None) =>
                   let '(addrb,ex_ids) := mk_tmp ex_ids in
                   let '(addre,ex_ids) := mk_tmp ex_ids in
                   (Some
                     (insn_call fake_id true false typ_void get_mmetadata_fn 
                       ((p8,(value_id ptmp))::
                        (pp8,(value_id addrb))::
                        (pp8,(value_id addre))::
                        (p8,vnullp8)::
                        (i32,vint1)::
                        (p32,vnullp32)::
                        nil)::
                      insn_load bid0 p8 (value_id addrb) Align.Zero::
                      insn_load eid0 p8 (value_id addre) Align.Zero::   
                      nil), ex_ids, addrb::addre::tmps, Some addrb, Some addre)
              | _ => (None, ex_ids, tmps, optaddrb, optaddre)
              end
          | None => (None, ex_ids, tmps, optaddrb, optaddre)
          end
        else (Some nil, ex_ids, tmps, optaddrb, optaddre) in
      match optcs with
      | None => None
      | Some cs =>
        Some (ex_ids, ptmp::btmp::etmp::tmps,
         insn_cast ptmp castop_bitcast (typ_pointer t2) v2 p8:: 
         insn_cast btmp castop_bitcast mt bv p8:: 
         insn_cast etmp castop_bitcast mt ev p8:: 
         insn_call fake_id true false typ_void assert_mptr_fn 
           ((p8,(value_id ptmp))::
            (p8,(value_id btmp))::
            (p8,(value_id etmp))::
            (i32,type_size t2)::
            (i32,vint1)::nil)::
         c::
         cs, optaddrb, optaddre)
      end
    | None => None
    end

| insn_store id0 t0 v1 v2 align =>
    match get_reg_metadata rm v2 with
    | Some (mt2, bv, ev) =>
      let '(ptmp,ex_ids) := mk_tmp ex_ids in
      let '(btmp,ex_ids) := mk_tmp ex_ids in
      let '(etmp,ex_ids) := mk_tmp ex_ids in
      let optcs := 
        if isPointerTypB t0 then
          match get_reg_metadata rm v1 with
          | Some (mt1, bv0, ev0) =>
              Some
                (insn_call fake_id true false typ_void set_mmetadata_fn 
                  ((p8,(value_id ptmp))::
                   (p8,bv0)::
                   (p8,ev0)::
                   (p8,vnullp8)::
                   (i32,vint1)::
                   (i32,vint1)::
                   nil)::
                 nil)
          | None => None
          end
        else Some nil in
      match optcs with
      | None => None
      | Some cs =>
        Some (ex_ids, ptmp::btmp::etmp::tmps,
         insn_cast ptmp castop_bitcast (typ_pointer t0) v2 p8:: 
         insn_cast btmp castop_bitcast mt2 bv p8:: 
         insn_cast etmp castop_bitcast mt2 ev p8:: 
         insn_call fake_id true false typ_void assert_mptr_fn 
           ((p8,(value_id ptmp))::
            (p8,(value_id btmp))::
            (p8,(value_id etmp))::
            (i32,(type_size t0))::
            (i32,vint1)::nil)::
         c::
         cs, optaddrb, optaddre)
      end
    | None => None
    end

| insn_gep id0 inbounds0 t1 v1 lv2 => 
    prop_metadata ex_ids tmps optaddrb optaddre rm c v1 id0

| insn_cast id0 op0 t1 v1 t2 => 
    match op0 with
    | castop_bitcast =>
        if isPointerTypB t1 then
          prop_metadata ex_ids tmps optaddrb optaddre rm c v1 id0
        else Some (ex_ids, tmps, [c], optaddrb, optaddre)
    | castop_inttoptr =>
        match lookupAL _ rm id0 with
        | Some (bid0, eid0) =>
            Some (ex_ids, tmps,
              c::
              insn_cast bid0 castop_bitcast p8 vnullp8 p8::
              insn_cast eid0 castop_bitcast p8 vnullp8 p8::
              nil, optaddrb, optaddre)
        | _ => None
        end
    | _ => Some (ex_ids, tmps, [c], optaddrb, optaddre)
    end

| insn_select id0 v0 t0 v1 v2 =>
    if isPointerTypB t0 then
      match (get_reg_metadata rm v1, get_reg_metadata rm v2, 
             lookupAL _ rm id0) with
      | (Some (mt1, bv1, ev1), Some (mt2, bv2, ev2), Some (bid0, eid0)) =>
          Some (ex_ids, tmps,
            c::
            insn_select bid0 v0 mt1 bv1 bv2:: 
            insn_select eid0 v0 mt1 ev1 ev2:: 
            nil, optaddrb, optaddre)
      | _ => None
      end
    else Some (ex_ids, tmps, [c], optaddrb, optaddre)

| insn_call id0 noret0 tailc0 rt fv lp =>
    match
      (match fv with
       | value_const (const_gid _ fid) =>
           if isSysLib fid then 
             Some (ex_ids, tmps, nil, nil) 
           else trans_params ex_ids tmps rm lp
       | _ => trans_params ex_ids tmps rm lp
       end) with
    | Some (ex_ids', tmps', cs, lp') =>
        Some (ex_ids', tmps', cs++[insn_call id0 noret0 tailc0 rt fv (lp++lp')],
              optaddrb, optaddre)
    | None => None
    end

| _ => Some (ex_ids, tmps, [c], optaddrb, optaddre)
end.

Fixpoint trans_cmds (ex_ids tmps:ids) (optaddrb optaddre:option id) (rm:rmap) 
  (cs:cmds) : option (ids*ids*cmds*option id*option id) :=
match cs with
| nil => Some (ex_ids, tmps, nil, optaddrb, optaddre)
| c::cs' =>
    match (trans_cmd ex_ids tmps optaddrb optaddre rm c) with
    | Some (ex_ids1, tmps1, cs1, optaddrb, optaddre) =>
        match (trans_cmds ex_ids1 tmps1 optaddrb optaddre rm cs') with
        | Some (ex_ids2, tmps2, cs2, optaddrb, optaddre) => 
            Some (ex_ids2, tmps2, cs1++cs2, optaddrb, optaddre)
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
    | Some (mt, bv, ev) =>
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

Definition trans_block (ex_ids tmps:ids) (optaddrb optaddre:option id) (rm:rmap)
  (b:block) : option (ids*ids*option id*option id*block) :=
let '(block_intro l1 ps1 cs1 tmn1) := b in
match trans_phinodes rm ps1 with
| None => None
| Some ps2 => 
    match trans_cmds ex_ids tmps optaddrb optaddre rm cs1 with
    | Some (ex_ids',tmps',cs2,optaddrb,optaddre) => 
        Some (ex_ids',tmps',optaddrb,optaddre,block_intro l1 ps2 cs2 tmn1)
    | None => None
    end
end.

Fixpoint trans_blocks (ex_ids tmps:ids) (optaddrb optaddre:option id) (rm:rmap) 
  (bs:blocks) : option (ids*ids*option id*option id*blocks) :=
match bs with
| nil => Some (ex_ids, tmps, optaddrb, optaddre, nil)
| b::bs' =>
    match (trans_block ex_ids tmps optaddrb optaddre rm b) with
    | Some (ex_ids1, tmps1, optaddrb, optaddre, b1) =>
        match (trans_blocks ex_ids1 tmps1 optaddrb optaddre rm bs') with
        | Some (ex_ids2, tmps2, optaddrb, optaddre, bs2) => 
            Some (ex_ids2, tmps2, optaddrb, optaddre, b1::bs2)
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
            Some ((p8,bid0)::(p8,eid0)::la2)
        | _ => None
        end
      else Some la2
    end
end.

Definition insert_more_allocas (optaddrb optaddre:option id) (b:block) : block :=
match (optaddrb, optaddre) with
| (Some addrb, Some addre) =>
  let '(block_intro l1 ps1 cs1 tmn1) := b in  
  block_intro l1 ps1
    (insn_alloca addrb p8 vint1 Align.Zero::
    insn_alloca addre p8 vint1 Align.Zero::cs1) tmn1
| _ => b
end.

Axiom rename_fid : id -> id.

Definition trans_fdef nts (f:fdef) : option (rmap*ids*fdef) :=
let '(fdef_intro (fheader_intro t fid la) bs) := f in
if SimpleSE.isCallLib fid then Some (nil, nil, f)
else
  let ex_ids := getFdefIDs f in
  match gen_metedata_fdef nts ex_ids nil f with
  | Some (ex_ids,rm) =>
      match (trans_args rm la) with
      | Some la' =>
          match (trans_blocks ex_ids nil None None rm bs) with
          | Some (ex_ids, tmps, optaddrb, optaddre, b'::bs') => 
              Some (rm, tmps, 
                fdef_intro 
                  (fheader_intro t (rename_fid fid) (la++la')) 
                  ((insert_more_allocas optaddrb optaddre b')::bs'))
          | _ => None
          end
      | _ => None
      end
  | None => None
  end.

Fixpoint trans_product nts (p:product) : option product :=
match p with
| product_fdef f =>
    match trans_fdef nts f with
    | None => None
    | Some (_,_,f') => Some (product_fdef f')
    end
| _ => Some p
end.

Fixpoint trans_products nts (ps:products) : option products :=
match ps with
| nil => Some nil
| p::ps' =>
    match (trans_product nts p) with
    | Some p1 =>
        match (trans_products nts ps') with
        | Some ps2 => Some (p1::ps2)
        | _ => None
        end
    | _ => None
    end
end.

Definition trans_module (m:module) : option module :=
let '(module_intro los nts ps) := m in
do ps' <- trans_products nts ps;
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

(* Simulation *)

Definition reg_simulation (rm1:SoftBound.rmetadata) (rm2:rmap) (lc1 lc2:GVMap) 
  : Prop :=
(forall i0 gv, lookupAL _ lc1 i0 = Some gv -> lookupAL _ lc2 i0 = Some gv) /\
(forall pid bgv egv, 
  lookupAL _ rm1 pid = Some (SoftBound.mkMD bgv egv) -> 
  exists bid, exists eid, 
    lookupAL _ rm2 pid = Some (bid, eid) /\
    lookupAL _ lc2 bid = Some bgv /\
    lookupAL _ lc2 eid = Some egv) /\
(forall pid bid eid bgv egv, 
  lookupAL _ rm2 pid = Some (bid, eid) ->
  lookupAL _ lc2 bid = Some bgv ->
  lookupAL _ lc2 eid = Some egv ->
  lookupAL _ rm1 pid = Some (SoftBound.mkMD bgv egv)).

Definition sb_meminj (b:Values.block) : option (Values.block * Z) :=
  Some (b, 0%Z).

Definition sb_mem_inj (M M':mem) := Memory.Mem.mem_inj sb_meminj M M'.

Definition mem_simulation TD (MM1:SoftBound.mmetadata) (Mem1 Mem2:mem) : Prop :=
sb_mem_inj Mem1 Mem2 /\
(forall lc gl b i bgv egv als lc' Mem2' tr addrb addre bid0 eid0 als' v, 
  MM1 b i = Some (SoftBound.mkMD bgv egv) ->
  getOperandValue TD Mem1 v lc gl = Some (ptr2GV TD (Vptr b i)) ->
  SimpleSE.dbCmds TD gl lc als Mem2
    (insn_call fake_id true false typ_void get_mmetadata_fn 
       ((p8,v)::
        (p8,(value_id addrb))::
        (p8,(value_id addre))::nil)::
     insn_load bid0 p8 (value_id addrb) Align.Zero::
     insn_load eid0 p8 (value_id addre) Align.Zero::   
     nil) lc' als' Mem2' tr ->
  lookupAL _ lc' bid0 = Some bgv /\
  lookupAL _ lc' bid0 = Some egv
) /\
(forall lc gl b i bgv egv als lc' Mem2' tr addrb addre bid0 eid0 als' v, 
  getOperandValue TD Mem1 v lc gl = Some (ptr2GV TD (Vptr b i)) ->
  SimpleSE.dbCmds TD gl lc als Mem2
    (insn_call fake_id true false typ_void get_mmetadata_fn 
       ((p8,v)::
        (p8,(value_id addrb))::
        (p8,(value_id addre))::nil)::
     insn_load bid0 p8 (value_id addrb) Align.Zero::
     insn_load eid0 p8 (value_id addre) Align.Zero::   
     nil) lc' als' Mem2' tr ->
  lookupAL _ lc' bid0 = Some bgv ->
  lookupAL _ lc' bid0 = Some egv ->
  MM1 b i = Some (SoftBound.mkMD bgv egv)
).

Fixpoint codom (rm:rmap) : atoms :=
match rm with
| nil => empty
| (_,(bid,eid))::rm' => singleton bid `union` singleton eid `union` codom rm'
end.

Lemma in_codom_of_rmap : forall rm2 pid bid eid,
  lookupAL (id * id) rm2 pid = ret (bid, eid) ->
  bid `in` codom rm2 /\ eid `in` codom rm2.
Proof.
  induction rm2; intros pid bid eid J.
    inversion J.  

    simpl in J.
    destruct a.
    destruct (pid == a); subst.
      inv J.
      simpl. auto.

      apply IHrm2 in J.
      destruct J as [J1 J2].
      simpl. destruct p.
      auto.
Qed.

Lemma reg_simulation__updateAddAL : forall rm1 rm2 lc1 lc2 i0 gv',
  reg_simulation rm1 rm2 lc1 lc2 ->
  i0 `notin` codom rm2 ->
  reg_simulation rm1 rm2 (updateAddAL GenericValue lc1 i0 gv')
    (updateAddAL GenericValue lc2 i0 gv').
Proof.
  intros rm1 rm2 lc1 lc2 i0 gv' Hsim Hnotin. 
  destruct Hsim as [J1 [J2 J3]].    
  split.
    intros i1 gv J.
    destruct (id_dec i0 i1); subst.
      rewrite lookupAL_updateAddAL_eq in *; auto.
    
      rewrite <- lookupAL_updateAddAL_neq in J; auto.
      rewrite <- lookupAL_updateAddAL_neq; auto.
  split.
    intros pid bbgv egv J.
    apply J2 in J. 
    destruct J as [bid [eid [J11 [J12 J13]]]].
    exists bid. exists eid.
    split; auto.
      apply in_codom_of_rmap in J11.    
      destruct J11 as [J11 J14].
      
      rewrite <- lookupAL_updateAddAL_neq; try solve [fsetdec].
      rewrite <- lookupAL_updateAddAL_neq; try solve [fsetdec].

    intros pid bid eid bgv egv H1 H2 H3.
    assert (H1':=H1).
    apply in_codom_of_rmap in H1'.    
    destruct H1' as [H11 H12].
    rewrite <- lookupAL_updateAddAL_neq in H2; try solve [fsetdec].
    rewrite <- lookupAL_updateAddAL_neq in H3; try solve [fsetdec].
    eauto.
Qed.


Definition sb_mem_inj__const2GV_prop (c:const) := forall Mem1 Mem2 TD gl gv,
  sb_mem_inj Mem1 Mem2 ->
  _const2GV TD Mem1 gl c = Some gv ->
  _const2GV TD Mem2 gl c = Some gv.

Definition sb_mem_inj__list_const2GV_prop (lc:list_const) := 
  forall Mem1 Mem2 TD gl,
  sb_mem_inj Mem1 Mem2 ->
  (forall gv, 
    _list_const_arr2GV TD Mem1 gl lc = Some gv ->
    _list_const_arr2GV TD Mem2 gl lc = Some gv) /\
  (forall R, 
    _list_const_struct2GV TD Mem1 gl lc = Some R ->
    _list_const_struct2GV TD Mem2 gl lc = Some R).

Lemma sb_mem_inj__const2GV_mutrec :
  (forall c, sb_mem_inj__const2GV_prop c) *
  (forall lc, sb_mem_inj__list_const2GV_prop lc).
Proof.
  apply const_mutrec; 
    unfold sb_mem_inj__const2GV_prop, sb_mem_inj__list_const2GV_prop;
    intros; simpl in *; eauto.

  apply H with (TD:=TD)(gl:=gl) in H0.
  destruct H0; eauto.

  apply H with (TD:=TD)(gl:=gl) in H0.
  destruct H0 as [H00 H01].
  remember (_list_const_struct2GV TD Mem1 gl l0) as R.
  destruct R as [[[gv1 t1] a1]|]; inv H1.
  erewrite H01; eauto.
  simpl. auto.

  remember (_const2GV TD Mem1 gl c) as R.
  destruct R as [[gv1 t1]|]; inv H1.
  erewrite H; eauto.
  simpl; auto.

  remember (_const2GV TD Mem1 gl c) as R.
  destruct R as [[gv1 t1]|]; inv H1.
  erewrite H; eauto.
  simpl; auto.

      remember (_const2GV TD Mem1 gl c0) as R.
      destruct R as [[gv1 t1]|]; inv H1.
      erewrite H; eauto.
      simpl.
      admit.

      remember (Constant.getTyp c) as R.
      destruct R; inv H2.       
      destruct t; inv H4.       
      remember (_const2GV TD Mem1 gl c) as R1.
      destruct R1 as [[gv1 t1]|]; inv H3.
      erewrite H; eauto.
      simpl. auto.

      remember (_const2GV TD Mem1 gl c) as R2.
      destruct R2 as [[gv2 t2]|]; inv H3.
      remember (_const2GV TD Mem1 gl c0) as R3.
      destruct R3 as [[gv3 t3]|]; inv H5.
      remember (_const2GV TD Mem1 gl c2) as R4.
      destruct R4 as [[gv4 t4]|]; inv H4.
      erewrite H; eauto.
      erewrite H0; eauto.
      erewrite H1; eauto.

      remember (_const2GV TD Mem1 gl c0) as R3.
      destruct R3 as [[gv3 t3]|]; inv H2.
      remember (_const2GV TD Mem1 gl c2) as R4.
      destruct R4 as [[gv4 t4]|]; inv H4.
      erewrite H; eauto.
      erewrite H0; eauto.
      simpl. auto.

      remember (_const2GV TD Mem1 gl c) as R3.
      destruct R3 as [[gv3 t3]|]; inv H2.
      remember (_const2GV TD Mem1 gl c0) as R4.
      destruct R4 as [[gv4 t4]|]; inv H4.
        erewrite H; eauto.
        erewrite H0; eauto.
        simpl. auto.

        destruct t3; inv H3.
      
  remember (_const2GV TD Mem1 gl c) as R.
  destruct R as [[gv1 t1]|]; inv H2.
  erewrite H; eauto.
  simpl; auto.

      remember (_const2GV TD Mem1 gl c) as R3.
      destruct R3 as [[gv3 t3]|]; inv H3.
      remember (_const2GV TD Mem1 gl c0) as R4.
      destruct R4 as [[gv4 t4]|]; inv H5.
      erewrite H; eauto.
      erewrite H0; eauto.
      simpl. auto.

      remember (_const2GV TD Mem1 gl c) as R3.
      destruct R3 as [[gv3 t3]|]; inv H2.
      remember (_const2GV TD Mem1 gl c0) as R4.
      destruct R4 as [[gv4 t4]|]; inv H4.
        erewrite H; eauto.
        erewrite H0; eauto.
        simpl. auto.

        destruct t3; inv H3.

      remember (_const2GV TD Mem1 gl c) as R3.
      destruct R3 as [[gv3 t3]|]; inv H2.
      remember (_const2GV TD Mem1 gl c0) as R4.
      destruct R4 as [[gv4 t4]|]; inv H4.
        erewrite H; eauto.
        erewrite H0; eauto.
        simpl. auto.

        destruct t3; inv H3.

  assert (H1':=H1).
  apply H0 with (TD:=TD)(gl:=gl) in H1'.
  destruct H1' as [H10 H11].
  split; intros.
    remember (_list_const_arr2GV TD Mem1 gl l0) as R3.
    destruct R3 as [[gv3 t3]|]; inv H2.
    remember (_const2GV TD Mem1 gl c) as R4.
    destruct R4 as [[gv4 t4]|]; inv H4.
    erewrite H; eauto.
    erewrite H10; eauto.
    simpl. auto.

    remember (_list_const_struct2GV TD Mem1 gl l0) as R3.
    destruct R3 as [[[gv3 t3] a3]|]; inv H2.
    remember (_const2GV TD Mem1 gl c) as R4.
    destruct R4 as [[gv4 t4]|]; inv H4.
    erewrite H; eauto.
    erewrite H11; eauto.
    simpl. auto.
Qed.

Lemma sb_mem_inj___const2GV : forall Mem1 Mem2 TD gl c gv,
  sb_mem_inj Mem1 Mem2 ->
  _const2GV TD Mem1 gl c = Some gv ->
  _const2GV TD Mem2 gl c = Some gv.
Proof.
  destruct sb_mem_inj__const2GV_mutrec as [J _].
  unfold sb_mem_inj__const2GV_prop in J. eauto.
Qed.

Lemma sb_mem_inj__const2GV : forall Mem Mem' TD gl c gv,
  sb_mem_inj Mem Mem' ->
  const2GV TD Mem gl c = Some gv ->
  const2GV TD Mem' gl c = Some gv.
Proof.
  intros.
  unfold const2GV in *.
  remember (_const2GV TD Mem0 gl c) as R.
  destruct R; try solve [inversion H0].
  destruct p.
  inv H0.
  symmetry in HeqR.
  erewrite sb_mem_inj___const2GV; eauto.
  simpl. auto.
Qed.

Lemma simulation__getOperandValue : forall rm rm2 lc lc2 TD MM Mem Mem2 gl v gv,
  reg_simulation rm rm2 lc lc2 ->
  mem_simulation TD MM Mem Mem2 ->
  getOperandValue TD Mem v lc gl = ret gv ->
  getOperandValue TD Mem2 v lc2 gl = ret gv.
Proof.
  intros rm rm2 lc lc2 TD MM Mem Mem2 gl v gv H1 H2 H3.
  unfold getOperandValue in *.
  destruct v.
    destruct H1 as [H1 _]; eauto.

    destruct H2 as [H2 _].
    eapply sb_mem_inj__const2GV; eauto.
Qed.

Lemma simulation__BOP : forall rm rm2 lc lc2 TD MM Mem Mem2 gl bop0 sz0 v1 v2 
                        gv3,
  reg_simulation rm rm2 lc lc2 ->
  mem_simulation TD MM Mem Mem2 ->
  BOP TD Mem lc gl bop0 sz0 v1 v2 = ret gv3 ->
  BOP TD Mem2 lc2 gl bop0 sz0 v1 v2 = ret gv3.
Proof.
  intros rm rm2 lc lc2 TD MM Mem Mem2 gl bop0 sz0 v1 v2 gv3 H1 H2 H3.
  unfold BOP in *.
  remember (getOperandValue TD Mem v1 lc gl) as R1.
  destruct R1; inv H3.
  remember (getOperandValue TD Mem v2 lc gl) as R2.
  destruct R2; inv H0.
  erewrite simulation__getOperandValue; eauto.
  erewrite simulation__getOperandValue; eauto.
Qed.

Lemma mem_simulation__malloc : forall TD MM Mem Mem2 tsz gn align0 Mem' mb,
  mem_simulation TD MM Mem Mem2 ->
  malloc TD Mem tsz gn align0 = ret (Mem', mb) ->
  exists Mem2', exists mb',
    malloc TD Mem2 tsz gn align0 = ret (Mem2', mb') /\
    mem_simulation TD MM Mem' Mem2'.
Proof.
  intros TD MM Mem Mem2 tsz gn align0 Mem' mb Hmsim Halloc.
  destruct Hmsim as [H1 [H2 H3]].
  unfold malloc in *.
  remember (GV2int TD Size.ThirtyTwo gn) as R.
  destruct R; try solve [inversion Halloc].
  remember (Mem.alloc Mem 0 (Size.to_Z tsz * z)) as R1.
  destruct R1 as [Mem1 mb1].
  inv Halloc.
  remember (Mem.alloc Mem2 0 (Size.to_Z tsz * z)) as R2.
  destruct R2 as [Mem2' mb2].
  exists Mem2'. exists mb2.
  split; auto.
  split.
    clear H2 H3.

unfold sb_mem_inj in *.
unfold sb_meminj in *.

Admitted.

Lemma mem_simulation__free : forall TD MM Mem Mem2 mptr0 Mem',
  mem_simulation TD MM Mem Mem2 ->
  free TD Mem mptr0 = ret Mem' ->
  exists Mem2',
    free TD Mem2 mptr0 = ret Mem2' /\
    mem_simulation TD MM Mem' Mem2'.
Admitted.

Lemma trans_cmd__is__correct : forall c TD lc1 rm1 als gl Mem1 MM1 lc1' als' 
    Mem1' MM1' tr lc2 Mem2 rm2 rm1' cs ex_ids tmps ex_ids' tmps' r
    optaddrb optaddre optaddrb' optaddre',  
  non_temporal_cmd c ->
  getCmdID c `notin` codom rm2 ->
  trans_cmd ex_ids tmps optaddrb optaddre rm2 c = 
    Some (ex_ids', tmps', cs, optaddrb', optaddre') ->
  reg_simulation rm1 rm2 lc1 lc2 ->
  mem_simulation TD MM1 Mem1 Mem2 ->
  SoftBound.dbCmd TD gl lc1 rm1 als Mem1 MM1 c lc1' rm1' als' Mem1' MM1' tr r ->
  exists lc2', exists Mem2',
   SimpleSE.dbCmds TD gl lc2 als Mem2 cs lc2' als' Mem2' tr /\
   reg_simulation rm1' rm2 lc1' lc2' /\
   mem_simulation TD MM1' Mem1' Mem2'.
Proof.
  intros c TD lc1 rm1 als gl Mem1 MM1 lc1' als' Mem1' MM1' tr lc2 Mem2 rm2 rm1' 
    cs ex_ids tmps ex_ids' tmps' r optaddrb optaddre optaddrb' optaddre' 
    Hnontemp Hnotin Htrans Hrsim Hmsim HdbCmd.
  (sb_dbCmd_cases (destruct HdbCmd) Case); simpl in Htrans;
    try solve [inversion Hnontemp].

Case "dbBop".
  inv Htrans.
  exists (updateAddAL GenericValue lc2 id0 gv3). exists Mem2. 
  split.
   assert (trace_nil = trace_app trace_nil trace_nil) as EQ. auto.
   rewrite EQ.
   eapply SimpleSE.dbCmds_cons; eauto.
     apply SimpleSE.dbBop; eauto using simulation__BOP.
  split; auto.
    apply reg_simulation__updateAddAL; auto.

admit. admit. admit.

Case "dbMalloc".
  remember (lookupAL (id * id) rm2 id0) as R1.
  destruct R1; try solve [inversion Htrans].
  destruct p as [bid eid].
  remember (mk_tmp ex_ids) as R2.
  destruct R2 as [tmp ex_ids''].
  inv Htrans.
  invert_prop_reg_metadata.
  apply mem_simulation__malloc with (MM:=MM)(Mem2:=Mem2) in H1; auto.
  destruct H1 as [Mem2' [mb' [H11 H12]]].
  exists 
    (updateAddAL _ 
      (updateAddAL _ 
        (updateAddAL _ 
          (updateAddAL GenericValue lc2 id0 (blk2GV TD mb'))
          bid (SoftBound.base2GV TD mb'))
        tmp (SoftBound.bound2GV TD mb' tsz n))
      eid (SoftBound.bound2GV TD mb' tsz n)).
  exists Mem2'.
  split.
    assert (trace_nil = trace_app trace_nil trace_nil) as EQ. auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL GenericValue lc2 id0 (blk2GV TD mb'))(als2:=als)
      (Mem2:=Mem2'); auto.
      apply SimpleSE.dbMalloc with (gn:=gn)(tsz:=tsz); 
        eauto using simulation__getOperandValue.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _
              (updateAddAL GenericValue lc2 id0 (blk2GV TD mb'))
              bid (SoftBound.base2GV TD mb')
      )
      (als2:=als)
      (Mem2:=Mem2'); auto.
      apply SimpleSE.dbCast; auto.
        admit.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _
              (updateAddAL _
                (updateAddAL GenericValue lc2 id0 (blk2GV TD mb'))
                 bid (SoftBound.base2GV TD mb'))
               tmp (SoftBound.bound2GV TD mb' tsz n)
      )
      (als2:=als)
      (Mem2:=Mem2'); auto.
      apply SimpleSE.dbGEP with (mp:=blk2GV TD mb')(vidxs:=[gn]); auto.
        admit. admit. admit.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _
              (updateAddAL _
                (updateAddAL _
                  (updateAddAL GenericValue lc2 id0 (blk2GV TD mb'))
                   bid (SoftBound.base2GV TD mb'))
                 tmp (SoftBound.bound2GV TD mb' tsz n))
               eid (SoftBound.bound2GV TD mb' tsz n)
      )
      (als2:=als)
      (Mem2:=Mem2'); auto.
      apply SimpleSE.dbCast; auto.
        admit.

  split; auto.
    admit.

Case "dbMalloc_error".
  admit.    

Case "dbAlloca".
  admit. 

Case "dbAlloca_error".
  admit. 

Case "dbLoad_nptr".
  remember (get_reg_metadata rm2 vp) as R.
  destruct R; try solve [inversion Htrans].
  destruct p as [bv ev].
  remember (mk_tmp ex_ids) as R1. 
  destruct R1 as [ptmp ex_ids1].
  remember (mk_tmp ex_ids1) as R2. 
  destruct R2 as [btmp ex_ids2].
  remember (mk_tmp ex_ids2) as R3. 
  destruct R3 as [etmp ex_ids3].
  remember (isPointerTypB t) as R4.
  destruct R4.
    unfold isPointerTyp in H3.
    rewrite <- HeqR4 in H3.
    contradict H3; auto.

    inv Htrans.
    admit.

Case "dbLoad_ptr".
  remember (get_reg_metadata rm2 vp) as R.
  destruct R; try solve [inversion Htrans].
  destruct p as [[mt bv] ev].
  remember (mk_tmp ex_ids) as R1. 
  destruct R1 as [ptmp ex_ids2].
  remember (mk_tmp ex_ids2) as R2. 
  destruct R2 as [btmp ex_ids3].
  remember (mk_tmp ex_ids3) as R3. 
  destruct R3 as [etmp ex_ids4].
  remember (isPointerTypB t) as R4.
  destruct R4.
    remember (lookupAL (id * id) rm2 id0) as R5.
    destruct R5; try solve [inversion Htrans].
    destruct p as [bid0 eid0].
    inv Htrans.
    admit.

    unfold isPointerTyp in H3.
    rewrite <- HeqR4 in H3.
    inversion H3.

admit. admit. admit.

Case "dbLoad_abort".
  remember (get_reg_metadata rm2 vp) as R.
  destruct R; try solve [inversion Htrans].
  destruct p as [[mt bv] ev].
  remember (mk_tmp ex_ids) as R1. 
  destruct R1 as [ptmp ex_ids2].
  remember (mk_tmp ex_ids2) as R2. 
  destruct R2 as [btmp ex_ids3].
  remember (mk_tmp ex_ids3) as R3. 
  destruct R3 as [etmp ex_ids4].
  remember (isPointerTypB t) as R4.
  destruct R4.
    remember (lookupAL (id * id) rm2 id0) as R5.
    destruct R5; try solve [inversion Htrans].
    destruct p as [bid0 eid0].
    inv Htrans.
    admit.

    inv Htrans.
    admit.

Case "dbStore_nptr".
  remember (get_reg_metadata rm2 vp) as R.
  destruct R; try solve [inversion Htrans].
  destruct p as [[mt bv] ev].
  remember (mk_tmp ex_ids) as R1. 
  destruct R1 as [ptmp ex_ids1].
  remember (mk_tmp ex_ids1) as R2. 
  destruct R2 as [btmp ex_ids2].
  remember (mk_tmp ex_ids2) as R3. 
  destruct R3 as [etmp ex_ids3].
  remember (isPointerTypB t) as R4.
  destruct R4.
    unfold isPointerTyp in H4.
    rewrite <- HeqR4 in H4.
    contradict H4; auto.

    inv Htrans.
    admit.

Case "dbStore_ptr".
  remember (get_reg_metadata rm2 vp) as R.
  destruct R; try solve [inversion Htrans].
  destruct p as [[mt bv] ev].
  remember (mk_tmp ex_ids) as R1. 
  destruct R1 as [ptmp ex_ids1].
  remember (mk_tmp ex_ids1) as R2. 
  destruct R2 as [btmp ex_ids2].
  remember (mk_tmp ex_ids2) as R3. 
  destruct R3 as [etmp ex_ids3].
  remember (isPointerTypB t) as R4.
  destruct R4.
    remember (get_reg_metadata rm2 v) as R5.
    destruct R5; try solve [inversion Htrans].
    destruct p as [[mt0 bv0] ev0].
    inv Htrans.
    admit.

    unfold isPointerTyp in H4.
    rewrite <- HeqR4 in H4.
    inversion H4.

admit. admit. admit.

Case "dbStore_abort".
  remember (get_reg_metadata rm2 vp) as R.
  destruct R; try solve [inversion Htrans].
  destruct p as [[mt bv] ev].
  remember (mk_tmp ex_ids) as R1. 
  destruct R1 as [ptmp ex_ids1].
  remember (mk_tmp ex_ids1) as R2. 
  destruct R2 as [btmp ex_ids2].
  remember (mk_tmp ex_ids2) as R3. 
  destruct R3 as [etmp ex_ids3].
  remember (isPointerTypB t) as R4.
  destruct R4.
    remember (get_reg_metadata rm2 v) as R5.
    destruct R5; try solve [inversion Htrans].
    destruct p as [bv0 ev0].
    inv Htrans.
    admit.

    inv Htrans.
    admit.

Admitted.

Fixpoint getCmdsIDs (cs:list cmd) : atoms :=
match cs with
| nil => empty
| c::cs' => singleton (getCmdID c) `union` getCmdsIDs cs'
end.

Lemma trans_cmds__is__correct : forall cs TD lc1 rm1 als gl Mem1 MM1 lc1' als' 
    Mem1' MM1' tr lc2 Mem2 rm2 rm1' cs' ex_ids tmps ex_ids' tmps' r
    optaddrb optaddre optaddrb' optaddre', 
  non_temporal_cmds cs ->
  AtomSetImpl.inter (getCmdsIDs cs) (codom rm2) [<=] empty ->
  trans_cmds ex_ids tmps optaddrb optaddre rm2 cs = 
    Some (ex_ids', tmps', cs', optaddrb', optaddre') ->
  reg_simulation rm1 rm2 lc1 lc2 ->
  mem_simulation TD MM1 Mem1 Mem2 ->
  SoftBound.dbCmds TD gl lc1 rm1 als Mem1 MM1 cs lc1' rm1' als' Mem1' MM1' tr r 
    ->
  exists lc2', exists Mem2',
    SimpleSE.dbCmds TD gl lc2 als Mem2 cs' lc2' als' Mem2' tr /\
    reg_simulation rm1' rm2 lc1' lc2' /\
    mem_simulation TD MM1' Mem1' Mem2'.
Admitted.

End SBpass.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)
