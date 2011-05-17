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

Definition gv_inject (mi: Values.meminj) (gv gv':GenericValue) : Prop :=
let '(vals,mks) := List.split gv in 
let '(vals',mks') := List.split gv' in 
val_list_inject mi vals vals' /\ mks = mks'.

Definition reg_simulation (mi:Values.meminj) (rm1:SoftBound.rmetadata) 
  (rm2:rmap) (lc1 lc2:GVMap) : Prop :=
(forall i0 gv1, 
  lookupAL _ lc1 i0 = Some gv1 -> 
  exists gv2, 
    lookupAL _ lc2 i0 = Some gv2 /\ gv_inject mi gv1 gv2
) /\
(forall pid bgv1 egv1, 
  lookupAL _ rm1 pid = Some (SoftBound.mkMD bgv1 egv1) -> 
  exists bid, exists eid, exists bgv2, exists egv2,
    lookupAL _ rm2 pid = Some (bid, eid) /\
    lookupAL _ lc2 bid = Some bgv2 /\
    lookupAL _ lc2 eid = Some egv2 /\
    gv_inject mi bgv1 bgv2 /\
    gv_inject mi egv1 egv2
) /\
(forall pid bid eid bgv2 egv2, 
  lookupAL _ rm2 pid = Some (bid, eid) ->
  lookupAL _ lc2 bid = Some bgv2 ->
  lookupAL _ lc2 eid = Some egv2 ->
  exists bgv1, exists egv1,
    lookupAL _ rm1 pid = Some (SoftBound.mkMD bgv1 egv1) /\
    gv_inject mi bgv1 bgv2 /\
    gv_inject mi egv1 egv2
).

Definition mem_simulation (mi:Values.meminj) TD (MM1:SoftBound.mmetadata) 
  (Mem1 Mem2:mem) : Prop :=
Mem.mem_inj mi Mem1 Mem2 /\
(forall lc2 gl b1 i1 bgv egv als addrb addre bid0 eid0 v b2 i2,  
  MM1 b1 i1 = Some (SoftBound.mkMD bgv egv) ->
  Values.val_inject mi (Vptr b1 i1) (Vptr b2 i2) ->
  getOperandValue TD Mem2 v lc2 gl = Some (ptr2GV TD (Vptr b2 i2)) ->
  exists bgv', exists egv', exists lc2', exists Mem2',
  SimpleSE.dbCmds TD gl lc2 als Mem2
    (insn_call fake_id true false typ_void get_mmetadata_fn 
       ((p8,v)::
        (p8,(value_id addrb))::
        (p8,(value_id addre))::nil)::
     insn_load bid0 p8 (value_id addrb) Align.Zero::
     insn_load eid0 p8 (value_id addre) Align.Zero::   
     nil) lc2' als Mem2' trace_nil /\
    lookupAL _ lc2' bid0 = Some bgv' /\
    lookupAL _ lc2' eid0 = Some egv' /\
    gv_inject mi bgv bgv' /\
    gv_inject mi egv egv' /\
    Mem.mem_inj mi Mem2 Mem2'
) /\
(forall lc2 gl b1 i1 als addrb addre bid0 eid0 v b2 i2,  
  MM1 b1 i1 = None ->
  Values.val_inject mi (Vptr b1 i1) (Vptr b2 i2) ->
  getOperandValue TD Mem2 v lc2 gl = Some (ptr2GV TD (Vptr b2 i2)) ->
  exists lc2', exists Mem2',
  SimpleSE.dbCmds TD gl lc2 als Mem2
    (insn_call fake_id true false typ_void get_mmetadata_fn 
       ((p8,v)::
        (p8,(value_id addrb))::
        (p8,(value_id addre))::nil)::
     insn_load bid0 p8 (value_id addrb) Align.Zero::
     insn_load eid0 p8 (value_id addre) Align.Zero::   
     nil) lc2' als Mem2' trace_nil /\
    lookupAL _ lc2' bid0 = Some null /\
    lookupAL _ lc2' eid0 = Some null /\
    Mem.mem_inj mi Mem2 Mem2'
) /\
(forall gl b2 i2 bgv' egv' als lc2 lc2' addrb addre bid0 eid0 v Mem2', 
  getOperandValue TD Mem2 v lc2 gl = Some (ptr2GV TD (Vptr b2 i2)) ->
  SimpleSE.dbCmds TD gl lc2 als Mem2
    (insn_call fake_id true false typ_void get_mmetadata_fn 
       ((p8,v)::
        (p8,(value_id addrb))::
        (p8,(value_id addre))::nil)::
     insn_load bid0 p8 (value_id addrb) Align.Zero::
     insn_load eid0 p8 (value_id addre) Align.Zero::   
     nil) lc2' als Mem2' trace_nil ->
  lookupAL _ lc2' bid0 = Some bgv' ->
  lookupAL _ lc2' eid0 = Some egv' ->
  exists bgv, exists egv, exists b1, exists i1,
    MM1 b1 i1 = Some (SoftBound.mkMD bgv egv) /\
    Values.val_inject mi (Vptr b1 i1) (Vptr b2 i2) /\
    gv_inject mi bgv bgv' /\
    gv_inject mi egv egv' /\
    Mem.mem_inj mi Mem2 Mem2'
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

Lemma reg_simulation__updateAddAL : forall mi rm1 rm2 lc1 lc2 i0 gv gv',
  reg_simulation mi rm1 rm2 lc1 lc2 ->
  i0 `notin` codom rm2 ->
  gv_inject mi gv gv' ->
  reg_simulation mi rm1 rm2 (updateAddAL GenericValue lc1 i0 gv)
    (updateAddAL GenericValue lc2 i0 gv').
Proof.
  intros mi rm1 rm2 lc1 lc2 i0 gv gv' Hsim Hnotin. 
  destruct Hsim as [J1 [J2 J3]].    
  split.
    intros i1 gv1 J.
    destruct (id_dec i0 i1); subst.
      rewrite lookupAL_updateAddAL_eq in *; auto.
      inv J.
      exists gv'. auto.
    
      rewrite <- lookupAL_updateAddAL_neq in J; auto.
      rewrite <- lookupAL_updateAddAL_neq; auto.
  split.
    intros pid bgv1 egv1 J.
    apply J2 in J. 
    destruct J as [bid [eid [bgv2 [egv2 [J11 [J12 [J13 [J14 J15]]]]]]]].
    exists bid. exists eid. exists bgv2. exists egv2.
    assert (J11':=J11).
    apply in_codom_of_rmap in J11'.    
    destruct J11' as [J16 J17].      
    rewrite <- lookupAL_updateAddAL_neq; try solve [fsetdec].
    rewrite <- lookupAL_updateAddAL_neq; try solve [fsetdec].
    split; auto.

    intros pid bid eid bgv2 egv2 H1 H2 H3.
    assert (H1':=H1).
    apply in_codom_of_rmap in H1'.    
    destruct H1' as [H11 H12].
    rewrite <- lookupAL_updateAddAL_neq in H2; try solve [fsetdec].
    rewrite <- lookupAL_updateAddAL_neq in H3; try solve [fsetdec].
    eauto.
Qed.

Lemma _zeroconst2GV__gv_inject_refl : forall TD t gv mi,
  _zeroconst2GV TD t = Some gv ->
  gv_inject mi gv gv.
Admitted.

Lemma gv_inject__eq__sizeGenericValue : forall mi gv1 gv2,
  gv_inject mi gv1 gv2 ->
  sizeGenericValue gv1 = sizeGenericValue gv2.
Admitted.

Lemma val_list_inject_app : forall mi vs1 vs1' vs2 vs2',
  val_list_inject mi vs1 vs2 ->
  val_list_inject mi vs1' vs2' ->
  val_list_inject mi (vs1++vs1') (vs2++vs2').
Admitted.

Lemma gv_inject_app : forall mi gv1 gv1' gv2 gv2',
  gv_inject mi gv1 gv2 ->
  gv_inject mi gv1' gv2' ->
  gv_inject mi (gv1++gv1') (gv2++gv2').
Admitted.

Lemma global_gv_inject_refl : forall mi gl i0 gv,
  lookupAL _ gl i0 = Some gv ->
  gv_inject mi gv gv.
Admitted.
    
Lemma simulation__mtrunc : forall mi TD top t1 gv1 t2 gv1' gv2,
  gv_inject mi gv1 gv1' ->
  mtrunc TD top t1 gv1 t2 = Some gv2 ->
  exists gv2',
    mtrunc TD top t1 gv1' t2 = Some gv2' /\
    gv_inject mi gv2 gv2'.
Admitted.

Lemma simulation__mext : forall mi TD eop t1 gv1 t2 gv1' gv2,
  gv_inject mi gv1 gv1' ->
  mext TD eop t1 gv1 t2 = Some gv2 ->
  exists gv2',
    mext TD eop t1 gv1' t2 = Some gv2' /\
    gv_inject mi gv2 gv2'.
Admitted.

Lemma simulation__mbop : forall mi TD op bsz gv1 gv1' gv2 gv2' gv3,
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  mbop TD op bsz gv1 gv2 = Some gv3 ->
  exists gv3',
    mbop TD op bsz gv1' gv2' = Some gv3' /\
    gv_inject mi gv3 gv3'.
Admitted.

Lemma simulation__mfbop : forall mi TD op fp gv1 gv1' gv2 gv2' gv3,
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  mfbop TD op fp gv1 gv2 = Some gv3 ->
  exists gv3',
    mfbop TD op fp gv1' gv2' = Some gv3' /\
    gv_inject mi gv3 gv3'.
Admitted.

Lemma simulation__mcast : forall mi TD Mem1 Mem2 op t1 gv1 gv1' t2 gv2,
  gv_inject mi gv1 gv1' ->
  Mem.mem_inj mi Mem1 Mem2 ->  
  mcast TD Mem1 op t1 gv1 t2 = Some gv2 ->
  exists gv2',
    mcast TD Mem2 op t1 gv1' t2 = Some gv2' /\
    gv_inject mi gv2 gv2'.
Admitted.

Lemma simulation__micmp : forall mi TD c t gv1 gv1' gv2 gv2' gv3,
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  micmp TD c t gv1 gv2 = Some gv3 ->
  exists gv3',
    micmp TD c t gv1' gv2' = Some gv3' /\
    gv_inject mi gv3 gv3'.
Admitted.

Lemma simulation__mfcmp : forall mi TD c t gv1 gv1' gv2 gv2' gv3,
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  mfcmp TD c t gv1 gv2 = Some gv3 ->
  exists gv3',
    mfcmp TD c t gv1' gv2' = Some gv3' /\
    gv_inject mi gv3 gv3'.
Admitted.

Lemma simulation__GV2ptr : forall mi TD gv1 gv1' v,
  gv_inject mi gv1 gv1' ->
  GV2ptr TD (getPointerSize TD) gv1 = Some v ->
  exists v',
    GV2ptr TD (getPointerSize TD) gv1' = Some v' /\
    Values.val_inject mi v v'.
Admitted.

Lemma simulation__mgep : forall mi TD v v' v0 t0 l1,
  Values.val_inject mi v v' ->
  mgep TD t0 v l1 = Some v0 ->
  exists v0',
    mgep TD t0 v' l1 = Some v0' /\
    Values.val_inject mi v0 v0'.
Admitted.
   
Lemma gv_inject__eq__isGVZero : forall mi TD gv gv',
  gv_inject mi gv gv' ->
  isGVZero TD gv = isGVZero TD gv'.
Admitted.

Lemma simulation__extractGenericValue : forall mi gv1 gv1' TD t1 l0 gv,
  gv_inject mi gv1 gv1' ->
  extractGenericValue TD t1 gv1 l0 = Some gv ->
  exists gv',
    extractGenericValue TD t1 gv1' l0 = Some gv' /\
    gv_inject mi gv gv'.
Admitted.

Lemma simulation__insertGenericValue : forall mi gv1 gv1' TD t1 l0 gv t2 gv2 
                                              gv2',
  gv_inject mi gv1 gv1' ->
  gv_inject mi gv2 gv2' ->
  insertGenericValue TD t1 gv1 l0 t2 gv2 = Some gv ->
  exists gv',
    insertGenericValue TD t1 gv1' l0 t2 gv2' = Some gv' /\
    gv_inject mi gv gv'.
Admitted.

Definition sb_mem_inj__const2GV_prop (c:const) := forall mi Mem1 Mem2 TD gl gv t,
  Mem.mem_inj mi Mem1 Mem2 ->
  _const2GV TD Mem1 gl c = Some (gv,t) ->
  exists gv',
    _const2GV TD Mem2 gl c = Some (gv',t) /\
    gv_inject mi gv gv'.

Definition sb_mem_inj__list_const2GV_prop (lc:list_const) := 
  forall mi Mem1 Mem2 TD gl,
  Mem.mem_inj mi Mem1 Mem2 ->
  (forall gv t, 
    _list_const_arr2GV TD Mem1 gl lc = Some (gv,t) ->
    exists gv',
      _list_const_arr2GV TD Mem2 gl lc = Some (gv',t) /\
      gv_inject mi gv gv'
  ) /\
  (forall gv t a, 
    _list_const_struct2GV TD Mem1 gl lc = Some (gv,t,a) ->
    exists gv',
      _list_const_struct2GV TD Mem2 gl lc = Some (gv',t,a) /\
      gv_inject mi gv gv'
  ).

Lemma sb_mem_inj__const2GV_mutrec :
  (forall c, sb_mem_inj__const2GV_prop c) *
  (forall lc, sb_mem_inj__list_const2GV_prop lc).
Proof.
  apply const_mutrec; 
    unfold sb_mem_inj__const2GV_prop, sb_mem_inj__list_const2GV_prop;
    intros; simpl in *; eauto.

  remember (_zeroconst2GV TD t) as R.
  destruct R; inv H0.
  exists gv. split; eauto using _zeroconst2GV__gv_inject_refl.

  inv H0.
  exists (val2GV TD
            (Vint (Size.to_nat s - 1)
               (Int.repr (Size.to_nat s - 1) (INTEGER.to_Z i0)))
            (AST.Mint (Size.to_nat s - 1))).
  split; try solve [auto | unfold val2GV, gv_inject; simpl; auto].

  destruct f; inv H0.
    exists (val2GV TD (Vfloat f0) AST.Mfloat32).
    split; try solve [auto | unfold val2GV, gv_inject; simpl; auto].

    exists (val2GV TD (Vfloat f0) AST.Mfloat64).
    split; try solve [auto | unfold val2GV, gv_inject; simpl; auto].

  remember (getTypeSizeInBits TD t) as R.
  destruct R; inv H0.
  exists (val2GV TD Vundef (AST.Mint (n - 1))).
  split; try solve [auto | unfold val2GV, gv_inject; simpl; auto].
  
  inv H0.
  exists (val2GV TD (Vptr Mem.nullptr (Int.repr 31 0)) (AST.Mint 31)).
  split; auto. 
    unfold val2GV, gv_inject; simpl.
    split; auto.
      apply val_cons_inject; auto.
      apply val_inject_ptr with (delta:=0); auto.
      admit. (* mi should map null to null. *)
 
  apply H with (TD:=TD)(gl:=gl) in H0.
  destruct H0; eauto.

  apply H with (TD:=TD)(gl:=gl) in H0.
  destruct H0 as [H00 H01].
  remember (_list_const_struct2GV TD Mem1 gl l0) as R.
  destruct R as [[[gv1 t1] a1]|]; inv H1.
  destruct (@H01 gv1 t1 a1) as [gv' [H02 H03]]; auto.
  rewrite H02; auto.
  erewrite <- gv_inject__eq__sizeGenericValue; eauto.
  remember (sizeGenericValue gv1) as R1.
  destruct R1; inv H2.
    exists (uninits (Align.to_nat a1)).
    split; auto.
      unfold uninits, gv_inject; simpl; auto.

    exists (gv' ++ uninits (Align.to_nat a1 - S R1)).
    split; auto.
      unfold uninits.
      apply gv_inject_app; auto.
        unfold gv_inject; simpl; auto.       

  remember (lookupAL GenericValue gl i0) as R.
  destruct R; inv H0.
  exists gv. split; eauto using global_gv_inject_refl.

  remember (_const2GV TD Mem1 gl c) as R.
  destruct R as [[gv1 t1']|]; inv H1.
  symmetry in HeqR.
  eapply H in HeqR; eauto.
  destruct HeqR as [gv' [J1 J2]].
  rewrite J1.
  remember (mtrunc TD t t1' gv1 t0) as R1.
  destruct R1; inv H3.
  symmetry in HeqR1.
  eapply simulation__mtrunc in HeqR1; eauto.
  destruct HeqR1 as [gv2' [J3 J4]].
  rewrite J3.
  exists gv2'. split; auto.

  remember (_const2GV TD Mem1 gl c) as R.
  destruct R as [[gv1 t1']|]; inv H1.
  symmetry in HeqR.
  eapply H in HeqR; eauto.
  destruct HeqR as [gv' [J1 J2]].
  rewrite J1.
  remember (mext TD e t1' gv1 t) as R1.
  destruct R1; inv H3.
  symmetry in HeqR1.
  eapply simulation__mext in HeqR1; eauto.
  destruct HeqR1 as [gv2' [J3 J4]].
  rewrite J3.
  exists gv2'. split; auto.

  remember (_const2GV TD Mem1 gl c0) as R.
  destruct R as [[gv1 t1']|]; inv H1.
  symmetry in HeqR.
  eapply H in HeqR; eauto.
  destruct HeqR as [gv' [J1 J2]].
  rewrite J1.
  remember (mcast TD Mem1 c t1' gv1 t) as R1.
  destruct R1; inv H3.
  symmetry in HeqR1.
  eapply simulation__mcast in HeqR1; eauto.
  destruct HeqR1 as [gv2' [J3 J4]].
  rewrite J3.
  exists gv2'. split; auto.

  remember (Constant.getTyp c) as R.
  destruct R; inv H2.       
  destruct t0; inv H4.       
  remember (_const2GV TD Mem1 gl c) as R1.
  destruct R1 as [[gv1 t1]|]; inv H3.
  remember (getConstGEPTyp l0 t0) as R2.
  destruct R2; inv H4.
  remember (GV2ptr TD (getPointerSize TD) gv1) as R3.
  destruct R3; inv H3.
  remember (intConsts2Nats TD l0) as R4.
  destruct R4; inv H4.
  remember (mgep TD t0 v l1) as R5.
  destruct R5; inv H3.
  symmetry in HeqR1.
  eapply H in HeqR1; eauto.
  destruct HeqR1 as [gv1' [J1 J2]].
  rewrite J1.
  symmetry in HeqR3.
  eapply simulation__GV2ptr in HeqR3; eauto.
  destruct HeqR3 as [v' [J3 J4]].
  rewrite J3.  
  symmetry in HeqR5.
  eapply simulation__mgep in HeqR5; eauto.
  destruct HeqR5 as [v0' [J5 J6]].
  rewrite J5.
  exists (ptr2GV TD v0').
  split; auto.
    unfold ptr2GV, val2GV, gv_inject. simpl. auto.

  remember (_const2GV TD Mem1 gl c) as R2.
  destruct R2 as [[gv2 t2]|]; inv H3.
  remember (_const2GV TD Mem1 gl c0) as R3.
  destruct R3 as [[gv3 t3]|]; inv H5.
  remember (_const2GV TD Mem1 gl c2) as R4.
  destruct R4 as [[gv4 t4]|]; inv H4.
  symmetry in HeqR2. 
  eapply H in HeqR2; eauto.
  destruct HeqR2 as [gv2' [J1 J2]].
  rewrite J1.
  symmetry in HeqR3. 
  eapply H0 in HeqR3; eauto.
  destruct HeqR3 as [gv3' [J3 J4]].
  rewrite J3.
  symmetry in HeqR4. 
  eapply H1 in HeqR4; eauto.
  destruct HeqR4 as [gv4' [J5 J6]].
  rewrite J5.
  erewrite <- gv_inject__eq__isGVZero; eauto.
  destruct (isGVZero TD gv2); inv H5.
    exists gv4'. split; auto.
    exists gv3'. split; auto.

  remember (_const2GV TD Mem1 gl c0) as R3.
  destruct R3 as [[gv3 t3]|]; inv H2.
  remember (_const2GV TD Mem1 gl c2) as R4.
  destruct R4 as [[gv4 t4]|]; inv H4.
  symmetry in HeqR3. 
  eapply H in HeqR3; eauto.
  destruct HeqR3 as [gv3' [J3 J4]].
  rewrite J3.
  symmetry in HeqR4. 
  eapply H0 in HeqR4; eauto.
  destruct HeqR4 as [gv4' [J5 J6]].
  rewrite J5.
  remember (micmp TD c t3 gv3 gv4) as R1.
  destruct R1; inv H3.
  symmetry in HeqR1.
  eapply simulation__micmp in HeqR1; eauto.
  destruct HeqR1 as [gv' [J7 J8]].
  rewrite J7.
  exists gv'. split; auto.

  remember (_const2GV TD Mem1 gl c) as R3.
  destruct R3 as [[gv3 t3]|]; inv H2.
  destruct t3; inv H4.
  remember (_const2GV TD Mem1 gl c0) as R4.
  destruct R4 as [[gv4 t4]|]; inv H3.
  symmetry in HeqR3. 
  eapply H in HeqR3; eauto.
  destruct HeqR3 as [gv3' [J3 J4]].
  rewrite J3.
  symmetry in HeqR4. 
  eapply H0 in HeqR4; eauto.
  destruct HeqR4 as [gv4' [J5 J6]].
  rewrite J5.
  remember (mfcmp TD f f0 gv3 gv4) as R1.
  destruct R1; inv H4.
  symmetry in HeqR1.
  eapply simulation__mfcmp in HeqR1; eauto.
  destruct HeqR1 as [gv' [J7 J8]].
  rewrite J7.
  exists gv'. split; auto.
     
  remember (_const2GV TD Mem1 gl c) as R.
  destruct R as [[gv1 t1]|]; inv H2.
  remember (Constant.getTyp c) as R1.
  destruct R1; inv H4.       
  remember (getSubTypFromConstIdxs l0 t0) as R2.
  destruct R2; inv H3.   
  remember (extractGenericValue TD t1 gv1 l0) as R3.
  destruct R3; inv H4.   
  symmetry in HeqR. 
  eapply H in HeqR; eauto.
  destruct HeqR as [gv1' [J1 J2]].
  rewrite J1.
  symmetry in HeqR3.
  eapply simulation__extractGenericValue in HeqR3; eauto.
  destruct HeqR3 as [gv' [J3 J4]].
  rewrite J3.
  exists gv'. split; auto.

  remember (_const2GV TD Mem1 gl c) as R.
  destruct R as [[gv1 t1]|]; inv H3.
  remember (_const2GV TD Mem1 gl c0) as R2.
  destruct R2 as [[gv2 t2]|]; inv H5.
  remember (Constant.getTyp c0) as R1.
  destruct R1; inv H4.       
  remember (insertGenericValue TD t1 gv1 l0 t2 gv2) as R3.
  destruct R3; inv H5.   
  symmetry in HeqR. 
  eapply H in HeqR; eauto.
  destruct HeqR as [gv1' [J1 J2]].
  rewrite J1.
  symmetry in HeqR2. 
  eapply H0 in HeqR2; eauto.
  destruct HeqR2 as [gv2' [J3 J4]].
  rewrite J3.
  symmetry in HeqR3.
  eapply simulation__insertGenericValue in HeqR3; eauto.
  destruct HeqR3 as [gv' [J5 J6]].
  rewrite J5.
  exists gv'. split; auto.

  remember (_const2GV TD Mem1 gl c) as R3.
  destruct R3 as [[gv3 t3]|]; inv H2.
  destruct t3; inv H4.
  remember (_const2GV TD Mem1 gl c0) as R4.
  destruct R4 as [[gv4 t4]|]; inv H3.
  symmetry in HeqR3. 
  eapply H in HeqR3; eauto.
  destruct HeqR3 as [gv3' [J3 J4]].
  rewrite J3.
  symmetry in HeqR4. 
  eapply H0 in HeqR4; eauto.
  destruct HeqR4 as [gv4' [J5 J6]].
  rewrite J5.
  remember (mbop TD b s gv3 gv4) as R1.
  destruct R1; inv H4.
  symmetry in HeqR1.
  eapply simulation__mbop in HeqR1; eauto.
  destruct HeqR1 as [gv' [J7 J8]].
  rewrite J7.
  exists gv'. split; auto.

  remember (_const2GV TD Mem1 gl c) as R3.
  destruct R3 as [[gv3 t3]|]; inv H2.
  destruct t3; inv H4.
  remember (_const2GV TD Mem1 gl c0) as R4.
  destruct R4 as [[gv4 t4]|]; inv H3.
  symmetry in HeqR3. 
  eapply H in HeqR3; eauto.
  destruct HeqR3 as [gv3' [J3 J4]].
  rewrite J3.
  symmetry in HeqR4. 
  eapply H0 in HeqR4; eauto.
  destruct HeqR4 as [gv4' [J5 J6]].
  rewrite J5.
  remember (mfbop TD f f0 gv3 gv4) as R1.
  destruct R1; inv H4.
  symmetry in HeqR1.
  eapply simulation__mfbop in HeqR1; eauto.
  destruct HeqR1 as [gv' [J7 J8]].
  rewrite J7.
  exists gv'. split; auto.

  split.
    intros gv t J.
    inv J.
    exists nil. unfold gv_inject. simpl. split; auto.
 
    intros gv t a J.
    inv J.
    exists nil. unfold gv_inject. simpl. split; auto.  

  assert (H1':=H1).
  apply H0 with (TD:=TD)(gl:=gl) in H1'.
  destruct H1' as [H10 H11].
  split; intros.
    remember (_list_const_arr2GV TD Mem1 gl l0) as R3.
    destruct R3 as [[gv3 t3]|]; inv H2.
    remember (_const2GV TD Mem1 gl c) as R4.
    destruct R4 as [[gv4 t4]|]; inv H4.
    symmetry in HeqR4.
    eapply H in HeqR4; eauto.
    destruct HeqR4 as [gv4' [J1 J2]].
    rewrite J1.
    destruct (@H10 gv3 t3) as [gv3' [J3 J4]]; auto.
    rewrite J3.
    destruct (getTypeAllocSize TD t4); inv H3.
    exists ((gv3' ++ gv4') ++ uninits (s - sizeGenericValue gv4')).
    erewrite <- gv_inject__eq__sizeGenericValue; eauto.
    split; auto.    
      apply gv_inject_app.
        apply gv_inject_app; auto.
          unfold uninits, gv_inject. simpl. auto.

    remember (_list_const_struct2GV TD Mem1 gl l0) as R3.
    destruct R3 as [[[gv3 t3] a3]|]; inv H2.
    remember (_const2GV TD Mem1 gl c) as R4.
    destruct R4 as [[gv4 t4]|]; inv H4.
    symmetry in HeqR4.
    eapply H in HeqR4; eauto.
    destruct HeqR4 as [gv4' [J1 J2]].
    rewrite J1.
    symmetry in HeqR3.
    destruct (@H11 gv3 t3 a3) as [gv3' [J3 J4]]; auto.
    rewrite J3.
    destruct (getABITypeAlignment TD t4); inv H3.
    destruct (getTypeAllocSize TD t4); inv H4.
    exists (gv3' ++
            [(Vundef, AST.Mint ((n - sizeGenericValue gv4') * 8 - 1))]
            ++ gv4' ++ uninits (s - sizeGenericValue gv4')).
    erewrite <- gv_inject__eq__sizeGenericValue; eauto.
    destruct (le_lt_dec n (Align.to_nat a3)); inv H3.
      simpl_env.
      split; auto.
        apply gv_inject_app; auto.
         apply gv_inject_app; auto.
            unfold gv_inject. simpl. auto.
         apply gv_inject_app; auto.
            unfold uninits, gv_inject. simpl. auto.

      simpl_env.
      split; auto.
        apply gv_inject_app; auto.
         apply gv_inject_app; auto.
            unfold gv_inject. simpl. auto.
         apply gv_inject_app; auto.
            unfold uninits, gv_inject. simpl. auto.
Qed.

Lemma sb_mem_inj___const2GV : forall mi Mem1 Mem2 TD gl c gv t,
  Mem.mem_inj mi Mem1 Mem2 ->
  _const2GV TD Mem1 gl c = Some (gv,t) ->
  exists gv',
    _const2GV TD Mem2 gl c = Some (gv',t) /\
    gv_inject mi gv gv'.
Proof.
  destruct sb_mem_inj__const2GV_mutrec as [J _].
  unfold sb_mem_inj__const2GV_prop in J. eauto.
Qed.

Lemma sb_mem_inj__const2GV : forall mi Mem Mem' TD gl c gv,
  Mem.mem_inj mi Mem Mem' ->
  const2GV TD Mem gl c = Some gv ->
  exists gv',
    const2GV TD Mem' gl c = Some gv' /\
    gv_inject mi gv gv'.
Proof.
  intros.
  unfold const2GV in *.
  remember (_const2GV TD Mem0 gl c) as R.
  destruct R; try solve [inversion H0].
  destruct p.
  inv H0.
  symmetry in HeqR.
  eapply sb_mem_inj___const2GV in HeqR; eauto.
  destruct HeqR as [gv' [J1 J2]].
  exists gv'. rewrite J1. auto.
Qed.

Lemma simulation__getOperandValue : forall mi rm rm2 lc lc2 TD MM Mem Mem2 gl v 
                                           gv,
  reg_simulation mi rm rm2 lc lc2 ->
  mem_simulation mi TD MM Mem Mem2 ->
  getOperandValue TD Mem v lc gl = ret gv ->
  exists gv', 
    getOperandValue TD Mem2 v lc2 gl = ret gv' /\
    gv_inject mi gv gv'.
Proof.
  intros mi rm rm2 lc lc2 TD MM Mem Mem2 gl v gv H1 H2 H3.
  unfold getOperandValue in *.
  destruct v.
    destruct H1 as [H1 _]; auto.

    destruct H2 as [H2 _].
    eapply sb_mem_inj__const2GV; eauto.
Qed.

Lemma simulation__BOP : forall mi rm rm2 lc lc2 TD MM Mem Mem2 gl bop0 sz0 v1 v2 
                        gv3,
  reg_simulation mi rm rm2 lc lc2 ->
  mem_simulation mi TD MM Mem Mem2 ->
  BOP TD Mem lc gl bop0 sz0 v1 v2 = ret gv3 ->
  exists gv3',
    BOP TD Mem2 lc2 gl bop0 sz0 v1 v2 = ret gv3' /\
    gv_inject mi gv3 gv3'.
Proof.  
  intros mi rm rm2 lc lc2 TD MM Mem Mem2 gl bop0 sz0 v1 v2 gv3 H1 H2 H3.
  unfold BOP in *.
  remember (getOperandValue TD Mem v1 lc gl) as R1.
  destruct R1; inv H3.
  remember (getOperandValue TD Mem v2 lc gl) as R2.
  destruct R2; inv H0.
  symmetry in HeqR1.
  eapply simulation__getOperandValue in HeqR1; eauto.
  destruct HeqR1 as [g' [J1 J2]].
  rewrite J1.
  symmetry in HeqR2.
  eapply simulation__getOperandValue in HeqR2; eauto.
  destruct HeqR2 as [g0' [J3 J4]].
  rewrite J3.
  eapply simulation__mbop in H3; eauto.
Qed.

Lemma alloc_getOperandValue_inv : forall Mem2 lo hi Mem2' mb2 TD v lc2 gl b2 i2,
  Mem.alloc Mem2 lo hi = (Mem2', mb2) ->
  getOperandValue TD Mem2' v lc2 gl = ret ptr2GV TD (Vptr b2 i2) ->
  (getOperandValue TD Mem2 v lc2 gl = ret ptr2GV TD (Vptr b2 i2) /\ mb2 <> b2)
    \/ b2 = mb2.
Admitted. 

Lemma gv_inject_incr:
  forall f1 f2 v v',
  inject_incr f1 f2 ->
  gv_inject f1 v v' ->
  gv_inject f2 v v'.
Proof.
  intros. 
  unfold gv_inject in *.
  destruct (split v).
  destruct (split v').
  destruct H0.
  split; eauto using val_list_inject_incr.
Qed.

Lemma mem_simulation__malloc : forall mi TD MM Mem Mem2 tsz gn align0 Mem' mb,
  mem_simulation mi TD MM Mem Mem2 ->
  malloc TD Mem tsz gn align0 = ret (Mem', mb) ->
  exists mi', exists Mem2', exists mb',
    malloc TD Mem2 tsz gn align0 = ret (Mem2', mb') /\
    mem_simulation mi' TD MM Mem' Mem2' /\
    Values.inject_incr mi mi' /\
    mi' mb = Some (mb', 0) /\
    (forall b, b <> mb -> mi b = mi' b).
Proof.
  intros mi TD MM Mem Mem2 tsz gn align0 Mem' mb Hmsim Halloc.
  destruct Hmsim as [H1 [H2 H3]].
  unfold malloc in *.
  remember (GV2int TD Size.ThirtyTwo gn) as R.
  destruct R; try solve [inversion Halloc].
  remember (Mem.alloc Mem 0 (Size.to_Z tsz * z)) as R1.
  destruct R1 as [Mem1 mb1].
  inv Halloc.
  remember (Mem.alloc Mem2 0 (Size.to_Z tsz * z)) as R2.
  destruct R2 as [Mem2' mb2].
  exists (fun b => if zeq b mb then Some (mb2,0%Z) else mi b).
  exists Mem2'. exists mb2.
  split; auto.
  assert (inject_incr mi (fun b : Z => if zeq b mb then ret (mb2, 0) else mi b))
    as Hinject_incr.
    unfold inject_incr.
    intros b b' d H.
    destruct (zeq b mb); subst; auto.
      admit. (* mi mb must be None. *)
  split; auto.
  Case "msim".
    split.    
    SCase "msim1".
      clear H2 H3.
      destruct H1.
      apply Mem.mk_mem_inj.
      SSCase "mi_access".
        intros b1 b2 d c ofs p J1 J2.
        destruct (zeq b1 mb); subst; inv J1.
        SSSCase "b1=mb".
          symmetry in HeqR1.
          symmetry in HeqR2.
          destruct J2 as [J21 J22].
          assert (0 <= ofs /\ ofs + size_chunk c <= Size.to_Z tsz * z) as EQ.
            destruct (Z_le_dec 0 ofs).
              destruct (Z_le_dec (ofs + size_chunk c) (Size.to_Z tsz * z)); auto.
                apply Mem.perm_alloc_3 with (ofs:=ofs+size_chunk c-1) (p:=p) in 
                  HeqR1; auto with zarith.
                unfold Mem.range_perm in J21.
                assert (ofs <= ofs + size_chunk c - 1 < ofs + size_chunk c) as J.
                  assert (J':=@Memdata.size_chunk_pos c).
                  auto with zarith.
                apply J21 in J.           
                contradict J; auto. 
              apply Mem.perm_alloc_3 with (ofs:=ofs) (p:=p) in HeqR1; 
                auto with zarith.
              unfold Mem.range_perm in J21.
              assert (ofs <= ofs < ofs + size_chunk c) as J.
                assert (J':=@Memdata.size_chunk_pos c).
                auto with zarith.
              apply J21 in J.           
              contradict J; auto. 

          apply Mem.valid_access_alloc_same with (chunk:=c)(ofs:=ofs+0) in HeqR2;
            auto with zarith.
            eapply Mem.valid_access_implies; eauto using perm_F_any.

        SSSCase "b1<>mb".
          eapply Mem.valid_access_alloc_other; eauto.
          eapply Mem.valid_access_alloc_inv with (b:=mb)(lo:=0)
            (hi:=Size.to_Z tsz * z)(p:=p) in J2; eauto.
          destruct (eq_block); subst; try solve [eauto | contradict n; auto].

      SSCase "mi_memval".
Transparent Mem.alloc.
        intros b1 ofs b2 d J1 J2.
        injection HeqR1. intros NEXT MEM.
        injection HeqR2. intros NEXT2 MEM2.
        destruct Mem2. destruct Mem2'. destruct Mem. destruct Mem'. 
        inv MEM.
        inv MEM2. clear HeqR1 HeqR2.
        simpl in *.
        unfold Mem.perm in *. simpl in *.
        clear maxaddress_pos0 conversion_props0 maxaddress_pos2 
              conversion_props2.
        unfold update.     
        destruct (zeq b1 nextblock1); subst; inv J1.
        SSSCase "b1=nextblock1".
          destruct (zeq b2 b2) as [e | n]; 
            try solve [contradict n; auto].
          apply memval_inject_undef.

        SSSCase "b1<>mb".
          destruct (zeq b2 nextblock); subst.
            admit. (* mi b1 cannot be Some nextblock if b1 <> nextblock1 *)

            apply Memdata.memval_inject_incr with (f:=mi); auto.
              apply mi_memval; auto.
                clear - J2 n.
                unfold update in J2.
                destruct (zeq b1 nextblock1); subst; 
                  try solve [auto | contradict n; auto].

Global Opaque Mem.alloc.

    split.    
    SCase "msim2".
      clear H1 H3.
      intros lc2 gl b1 i1 bgv egv als addrb0 addre0 bid0 eid0 v b2 i2 J1 J2 J3.
      eapply alloc_getOperandValue_inv in J3; eauto.
      destruct J3 as [[J31 J32] | J3]; subst.
      SSCase "mb2 <> b2".
        assert (val_inject mi (Vptr b1 i1) (Vptr b2 i2)) as J.
          inversion J2; subst.
          destruct (zeq b1 mb); subst; eauto.
            inv H3. contradict J32; auto.
        destruct (@H2 lc2 gl b1 i1 bgv egv als addrb0 addre0 bid0 eid0 v b2 i2
          J1 J J31) as 
          [bgv' [egv' [lc2' [Mem21 [J37 [J33 [J34 [J35 [J36 J38]]]]]]]]].
        clear H2.
        assert (exists Mem21', 
          dbCmds TD gl lc2 als Mem2'
             (insn_call fake_id true false typ_void get_mmetadata_fn
                ((p8, v)
                 :: (p8, value_id addrb0) :: (p8, value_id addre0) :: nil)
              :: insn_load bid0 p8 (value_id addrb0) Align.Zero
                 :: insn_load eid0 p8 (value_id addre0) Align.Zero :: nil)
             lc2' als Mem21' trace_nil) as J'.
          admit. (* get_mmetadata_fn's axiom *)
        destruct J' as [Mem21' J'].
        exists bgv'. exists egv'. exists lc2'. exists Mem21'.
        split; auto.
        split; auto.
        split; auto.
        split; eauto using gv_inject_incr.
        split; eauto using gv_inject_incr.
          clear - J' J37 J38 HeqR2.
          admit. (* ?! *) 

      SSCase "mb2 = b2".
        inversion J2; subst.
        destruct (zeq b1 mb); subst.
          admit . (* wf MM should map mb i1 to None. *)
          admit.  (* wf mi should not map b1 (<>mb) to mb2 *)

    SCase "msim3".
      admit.

  split; auto.
  split.
    destruct (zeq mb mb); auto.
      contradict n; auto.

    intros.
    destruct (zeq b mb); subst; auto.
      contradict H; auto.
Qed.

Lemma malloc_getOperandValue_inv2 : 
  forall Mem2 tsz gn a0 Mem2' TD v lc2 gl gv mb2,
  malloc TD Mem2 tsz gn a0 = Some (Mem2', mb2) ->
  getOperandValue TD Mem2 v lc2 gl = Some gv ->
  getOperandValue TD Mem2' v lc2 gl = Some gv.
Admitted. 

Lemma simulation__eq__GV2int : forall mi gn gn' TD,
  gv_inject mi gn gn' ->
  GV2int TD Size.ThirtyTwo gn = GV2int TD Size.ThirtyTwo gn'.
Admitted.

Lemma simulation__mload : forall mi TD MM Mem0 Mem2 gvp align0 gv t gvp2,
  mem_simulation mi TD MM Mem0 Mem2 ->
  mload TD Mem0 gvp t align0 = ret gv ->
  gv_inject mi gvp gvp2 ->
  exists gv2, mload TD Mem2 gvp2 t align0 = ret gv2 /\ gv_inject mi gv gv2.
Admitted.

Lemma trans_cmd__is__correct__dbMalloc : forall 
  (lc2 : GVMap)
  (Mem2 : mem)
  (rm2 : rmap)
  (cs : cmds)
  (ex_ids : ids)
  (tmps : ids)
  (ex_ids' : ids)
  (tmps' : ids)
  (optaddrb : monad id)
  (optaddre : monad id)
  (optaddrb' : monad id)
  (optaddre' : monad id)
  (mi : meminj)
  (id0 : atom)
  (t : typ)
  (v : value)
  (align0 : align)
  (Hnontemp : non_temporal_cmd (insn_malloc id0 t v align0))
  (Hnotin : getCmdID (insn_malloc id0 t v align0) `notin` codom rm2)
  (Htrans : trans_cmd ex_ids tmps optaddrb optaddre rm2
             (insn_malloc id0 t v align0) =
           ret (ex_ids', tmps', cs, optaddrb', optaddre'))
  (rm : AssocList SoftBound.metadata)
  (lc : GVMap)
  (Hrsim : reg_simulation mi rm rm2 lc lc2)
  (TD : TargetData)
  (Mem0 : mem)
  (MM : SoftBound.mmetadata)
  (Hmsim : mem_simulation mi TD MM Mem0 Mem2)
  (gl : GVMap)
  (gn : GenericValue)
  (als : list mblock)
  (Mem' : mem)
  (tsz : sz)
  (mb : mblock)
  (lc' : GVMap)
  (rm' : SoftBound.rmetadata)
  (n : Z)
  (H : getTypeAllocSize TD t = ret tsz)
  (H0 : getOperandValue TD Mem0 v lc gl = ret gn)
  (H1 : malloc TD Mem0 tsz gn align0 = ret (Mem', mb))
  (H2 : GV2int TD Size.ThirtyTwo gn = ret n)
  (H3 : SoftBound.prop_reg_metadata lc rm id0 (blk2GV TD mb)
         {|
         SoftBound.md_base := SoftBound.base2GV TD mb;
         SoftBound.md_bound := SoftBound.bound2GV TD mb tsz n |} = 
       (lc', rm')),
   exists lc2' : GVMap,
     exists Mem2' : mem,
       exists mi' : meminj,
         dbCmds TD gl lc2 als Mem2 cs lc2' als Mem2' trace_nil /\
         reg_simulation mi' rm' rm2 lc' lc2' /\
         mem_simulation mi' TD MM Mem' Mem2' /\ inject_incr mi mi'.
Proof.
  intros.
  simpl in Htrans.
  remember (lookupAL (id * id) rm2 id0) as R1.
  destruct R1; try solve [inversion Htrans].
  destruct p as [bid eid].
  remember (mk_tmp ex_ids) as R2.
  destruct R2 as [tmp ex_ids''].
  inv Htrans.
  invert_prop_reg_metadata.
  apply mem_simulation__malloc with (MM:=MM)(Mem2:=Mem2)(mi:=mi) in H1; auto.
  destruct H1 as [mi' [Mem2' [mb' [H11 [H12 [H13 [H14 H15]]]]]]].
  exists 
    (updateAddAL _ 
      (updateAddAL _ 
        (updateAddAL _ 
          (updateAddAL GenericValue lc2 id0 (blk2GV TD mb'))
          bid (SoftBound.base2GV TD mb'))
        tmp (SoftBound.bound2GV TD mb' tsz n))
      eid (SoftBound.bound2GV TD mb' tsz n)).
  exists Mem2'. exists mi'.
  split.
  SCase "dbCmds".
    assert (trace_nil = trace_app trace_nil trace_nil) as EQ. auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL GenericValue lc2 id0 (blk2GV TD mb'))(als2:=als)
      (Mem2:=Mem2'); auto.
      eapply simulation__getOperandValue in H0; eauto.
      destruct H0 as [gn' [H00 H01]].
      unfold malloc in H11.
      erewrite simulation__eq__GV2int in H11; eauto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _
              (updateAddAL GenericValue lc2 id0 (blk2GV TD mb'))
              bid (SoftBound.base2GV TD mb')
      )
      (als2:=als)
      (Mem2:=Mem2'); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. simpl.
        rewrite lookupAL_updateAddAL_eq.
        auto.
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

      assert (exists gn', getOperandValue TD Mem2' v lc2 gl = ret gn' /\
                          gv_inject mi gn gn') as H4.
        eapply simulation__getOperandValue with (MM:=MM)(Mem2:=Mem2) in H0
          ; eauto.
        destruct H0 as [gv' [H00 H01]].
        apply malloc_getOperandValue_inv2 with (tsz:=tsz)(gn:=gn)(a0:=align0)
         (Mem2':=Mem2')(mb2:=mb') in H00; auto.
        exists gv'. auto.
      destruct H4 as [gn' [H41 H42]].
      apply SimpleSE.dbGEP with (mp:=blk2GV TD mb')(vidxs:=[gn']); auto.
        simpl.
        rewrite <- lookupAL_updateAddAL_neq.
          rewrite lookupAL_updateAddAL_eq; auto.
          admit. (*id0 <> bid*)

        simpl.
        assert(getOperandValue TD Mem2' v
          (updateAddAL _ (updateAddAL _ lc2 id0 (blk2GV TD mb'))
          bid (SoftBound.base2GV TD mb')) gl = 
          getOperandValue TD Mem2' v lc2 gl) as EQ'.
          admit. (* id0 and bid are not in v *)
        rewrite EQ'. clear EQ'.
        rewrite H41. auto.

        unfold SoftBound.bound2GV, GEP, blk2GV, GV2ptr, ptr2GV, val2GV.
        simpl.
        erewrite simulation__eq__GV2int in H2; eauto.
        rewrite H2.
        unfold mgetoffset. destruct TD.
        unfold typ2utyp. simpl.
        assert (exists ut, typ2utyp_aux (gen_utyp_maps (rev n0)) t = Some ut)
          as H5.       
          admit. (* wft *)
        destruct H5 as [ut H5]. 
        rewrite H5. simpl.
        assert (getTypeAllocSize (l0, n0) t = 
          getTypeAllocSize (l0, n0) (utyp2typ ut)) as H6.
          admit. (* ?! *)
        rewrite <- H6.
        rewrite H. simpl.
        rewrite Int.add_commut.
        rewrite Int.add_zero. auto.

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
        unfold CAST. simpl.
        rewrite lookupAL_updateAddAL_eq; auto.

  split; auto.
  SCase "rsim".
    clear - Hrsim H13 H14 H15 subcase.
    split.
      intros i0 gv1 J.
      destruct (id_dec id0 i0); subst.
      SSCase "id0 = i0".
        rewrite lookupAL_updateAddAL_eq in J.
        inv J.
        exists (blk2GV TD mb').
        split.
          admit. (* i0 <> bid eid tmp *)
 
          unfold gv_inject, blk2GV, ptr2GV, val2GV.
          simpl.
          split; eauto.
           
      SSCase "id0 <> i0".
        rewrite <- lookupAL_updateAddAL_neq in J; auto.
        destruct Hrsim as [J1 _].
        apply J1 in J.
        destruct J as [gv2 [J J2]].
        exists gv2.
        split.
          admit. (* i0 <> bid eid tmp *)

          eapply gv_inject_incr; eauto.

      admit. (* lets see if the proofs need this direction. *)
Qed.

Lemma trans_cmd__is__correct__dbLoad_nptr__case : forall b0 i1 TD s t
  b b1 i0 i2,
  ret Vptr b0 i1 = GV2ptr TD (getPointerSize TD) null ->
  ret Vptr b1 i2 = GV2ptr TD (getPointerSize TD) null  ->
  ret s = getTypeAllocSize TD t ->
  zeq b b0 && zeq b0 b1 && zle (Int.signed 31 i1) (Int.signed 31 i0) &&
  zle (Int.signed 31 i0 + Size.to_Z s) (Int.signed 31 i2) ->
  False.
Proof.  
  intros.
  simpl in *.
  inv H. inv H0.
  (* H2 is false since Size.to_Z s is pos. *)
Admitted.  

Lemma trans_cmd__is__correct__dbLoad_nptr : forall
  (lc2 : GVMap)
  (Mem2 : mem)
  (rm2 : rmap)
  (cs : cmds)
  (ex_ids : ids)
  (tmps : ids)
  (ex_ids' : ids)
  (tmps' : ids)
  (optaddrb : monad id)
  (optaddre : monad id)
  (optaddrb' : monad id)
  (optaddre' : monad id)
  (mi : meminj)
  (id0 : id)
  (t : typ)
  (vp : value)
  (align0 : align)
  (Hnontemp : non_temporal_cmd (insn_load id0 t vp align0))
  (Hnotin : getCmdID (insn_load id0 t vp align0) `notin` codom rm2)
  (Htrans : trans_cmd ex_ids tmps optaddrb optaddre rm2
             (insn_load id0 t vp align0) =
           ret (ex_ids', tmps', cs, optaddrb', optaddre'))
  (rm : SoftBound.rmetadata)
  (lc : GVMap)
  (Hrsim : reg_simulation mi rm rm2 lc lc2)
  (TD : TargetData)
  (Mem0 : mem)
  (MM : SoftBound.mmetadata)
  (Hmsim : mem_simulation mi TD MM Mem0 Mem2)
  (gl : GVMap)
  (als : list mblock)
  (gvp : GenericValue)
  (md : SoftBound.metadata)
  (gv : GenericValue)
  (H : SoftBound.get_reg_metadata TD Mem0 gl rm vp = md)
  (H0 : getOperandValue TD Mem0 vp lc gl = ret gvp)
  (H1 : SoftBound.assert_mptr TD t gvp md)
  (H2 : mload TD Mem0 gvp t align0 = ret gv)
  (H3 : ~ isPointerTyp t),
   exists lc2' : GVMap,
     exists Mem2' : mem,
       exists mi' : meminj,
         dbCmds TD gl lc2 als Mem2 cs lc2' als Mem2' trace_nil /\
         reg_simulation mi' rm rm2 (updateAddAL GenericValue lc id0 gv) lc2' /\
         mem_simulation mi' TD MM Mem0 Mem2' /\ inject_incr mi mi'.
Proof.
  intros.
  simpl in Htrans.
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
  SCase "t is ptr".
    unfold isPointerTyp in H3.
    rewrite <- HeqR4 in H3.
    contradict H3; auto.

  SCase "t isnt ptr".
  inv Htrans.
  assert (J:=H1).
  unfold SoftBound.assert_mptr in J.
  case_eq (SoftBound.get_reg_metadata TD Mem0 gl rm vp).
  intros md_base md_bound J1.
  rewrite J1 in J.

  remember (GV2ptr TD (getPointerSize TD) gvp) as R.
  destruct R; try solve [inversion J].
  destruct v; try solve [inversion J].
  remember (GV2ptr TD (getPointerSize TD) md_base) as R1.
  destruct R1; try solve [inversion J].
  destruct v; try solve [inversion J].
  remember (GV2ptr TD (getPointerSize TD) md_bound) as R2.
  destruct R2; try solve [inversion J].
  destruct v; try solve [inversion J].
  remember (getTypeAllocSize TD t) as R3.
  destruct R3; try solve [inversion J].
  eapply simulation__getOperandValue in H0; eauto.
  destruct H0 as [gvp2 [H00 H01]].            
  unfold SoftBound.get_reg_metadata in J1.
  eapply simulation__mload in H2; eauto.
  destruct H2 as [gv2 [H21 H22]].
  destruct Hrsim as [Hrsim1 [Hrsim2 Hrsim3]].
  destruct vp as [pid |].
    SSCase "vp is value_id".
    remember (lookupAL SoftBound.metadata rm pid) as R4.
    destruct R4; subst.
      SSSCase "pid is in rm".
      symmetry in HeqR8.
      assert (HeqR8':=HeqR8).
      apply Hrsim2 in HeqR8'.      
      destruct HeqR8' as [bid [eid [bgv2 [egv2 [J1 [J2 [J3 [J4 J5]]]]]]]].
      exists 
       (updateAddAL _ 
        (updateAddAL _ 
          (updateAddAL _ 
           (updateAddAL GenericValue lc2 ptmp gvp2)
           btmp bgv2)
          etmp egv2)
        id0 gv2).
      exists Mem2. exists mi.
      split.
        SSSSCase "dbCmds".

    assert (trace_nil = trace_app trace_nil trace_nil) as EQ. auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with (lc2:=updateAddAL GenericValue lc2 ptmp gvp2)
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. simpl. simpl in H00.
        rewrite H00. auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) btmp bgv2)(als2:=als)
      (Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. 
        simpl in HeqR. rewrite J1 in HeqR. inv HeqR.
        simpl.
        rewrite <- lookupAL_updateAddAL_neq; auto.
          rewrite J2. auto.
          admit. (* fresh id *)
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2)
              btmp bgv2) etmp egv2)
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. 
        simpl in HeqR. rewrite J1 in HeqR. inv HeqR.
        simpl.
        rewrite <- lookupAL_updateAddAL_neq; auto.
          rewrite <- lookupAL_updateAddAL_neq; auto.
            rewrite J3. auto.
            admit. (* fresh id *)
          admit. (* fresh id *)
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) btmp bgv2)
        etmp egv2)
      (als2:=als)(Mem2:=Mem2); auto.
       clear - H00 J1 J2 J3 J4 J5 J H00 H01 HeqR0 HeqR5 HeqR6.
       admit. (* assert_mptr_fn' axiom. *)
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ 
        (updateAddAL _ lc2 ptmp gvp2) btmp bgv2) etmp egv2) id0 gv2)
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbLoad with (mp:=gvp2); auto.
        simpl.
        rewrite <- lookupAL_updateAddAL_neq; auto.
        rewrite <- lookupAL_updateAddAL_neq; auto.
        rewrite <- lookupAL_updateAddAL_neq; auto.
          admit. (* fresh id *)
          admit. (* fresh id *)
          admit. (* fresh id *)

      split; auto.
        SSSSCase "rsim".

    clear - Hrsim1 H22 subcase subsubcase subsubsubcase subsubsubsubcase.
    split.
          SSSSSCase "rsim1".
      intros i0 gv1 J.
      destruct (id_dec id0 i0); subst.
        rewrite lookupAL_updateAddAL_eq in J.
        inv J.
        exists gv2.
        split; auto.
          admit. (* i0 <> btmp etmp ptmp *)
 
        rewrite <- lookupAL_updateAddAL_neq in J; auto.
        apply Hrsim1 in J.
        destruct J as [gv2' [J J2]].
        exists gv2'.
        split; auto.
          admit. (* i0 <> bid eid tmp *)

          SSSSSCase "rsim2".
      admit. (* lets see if the proofs need this direction. *)

      SSSCase "pid isnt in rm".
      inv J1.
      eapply trans_cmd__is__correct__dbLoad_nptr__case in J; eauto.
      inversion J.

    SSCase "vp is value_const".
    remember (SoftBound.get_const_metadata c) as R.
    destruct R. 
      destruct p as [bc ec].
      remember (const2GV TD Mem0 gl bc) as R1.
      remember (const2GV TD Mem0 gl ec) as R2.
      destruct R1; simpl in J1.       
        destruct R2; simpl in J1.
          inv J1.
          simpl in HeqR.
          rewrite <- HeqR8 in HeqR.
          remember (Constant.getTyp c) as R3.
          destruct R3; inv HeqR.
          symmetry in HeqR10, HeqR9.
          assert (Hmject:=Hmsim).
          destruct Hmject as [Hmject _].
          apply sb_mem_inj__const2GV with (Mem':=Mem2)(mi:=mi) in HeqR10; auto.
          apply sb_mem_inj__const2GV with (Mem':=Mem2)(mi:=mi) in HeqR9; auto.
          destruct HeqR10 as [mb_bound' [HeqR100 HeqR101]].            
          destruct HeqR9 as [mb_base' [HeqR90 HeqR91]].           
          exists 
           (updateAddAL _ 
            (updateAddAL _ 
             (updateAddAL _ 
              (updateAddAL GenericValue lc2 ptmp gvp2)
              btmp mb_base')
             etmp mb_bound')
            id0 gv2).
           exists Mem2. exists mi.
           split.
           SSSCase "dbCmds".

    assert (trace_nil = trace_app trace_nil trace_nil) as EQ. auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with (lc2:=updateAddAL GenericValue lc2 ptmp gvp2)
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. simpl. simpl in H00.
        rewrite H00. auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) btmp mb_base')(als2:=als)
      (Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. simpl. rewrite HeqR90.
        clear - HeqR8 HeqR11.
        admit. (* given wf typ, t0 must be of ptr. *)
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2)
              btmp mb_base') etmp mb_bound')
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. simpl. rewrite HeqR100.
        clear - HeqR8 HeqR11.
        admit. (* given wf typ, t0 must be of ptr. *)
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) btmp 
        mb_base') etmp mb_bound') (als2:=als)(Mem2:=Mem2); auto.
       clear - J HeqR0 HeqR5 HeqR6 H00 H00 H01 HeqR100 HeqR101 HeqR90 HeqR91.
       admit. (* assert_mptr_fn' axiom. *)
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ 
        (updateAddAL _ lc2 ptmp gvp2) btmp mb_base') etmp mb_bound') id0 gv2)
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbLoad with (mp:=gvp2); auto.

           split; auto.
        SSSCase "rsim".

    clear - Hrsim1 H22 subcase subsubcase subsubsubcase.
    split.
          SSSSSCase "rsim1".
      intros i0 gv1 J.
      destruct (id_dec id0 i0); subst.
        rewrite lookupAL_updateAddAL_eq in J.
        inv J.
        exists gv2.
        split; auto.
          admit. (* i0 <> btmp etmp ptmp *)
 
        rewrite <- lookupAL_updateAddAL_neq in J; auto.        
        apply Hrsim1 in J.
        destruct J as [gv2' [J J2]].
        exists gv2'.
        split; auto.
          admit. (* i0 <> bid eid tmp *)

          SSSSSCase "rsim2".
      admit. (* lets see if the proofs need this direction. *)

          inv J1.
          eapply trans_cmd__is__correct__dbLoad_nptr__case in J; eauto.
          inversion J.

        inv J1.
        eapply trans_cmd__is__correct__dbLoad_nptr__case in J; eauto.
        inversion J.
        
      inv J1.
      eapply trans_cmd__is__correct__dbLoad_nptr__case in J; eauto.
      inversion J.
Qed.

Lemma trans_cmd__is__correct : forall c TD lc1 rm1 als gl Mem1 MM1 lc1' als' 
    Mem1' MM1' tr lc2 Mem2 rm2 rm1' cs ex_ids tmps ex_ids' tmps' r
    optaddrb optaddre optaddrb' optaddre' mi,  
  non_temporal_cmd c ->
  getCmdID c `notin` codom rm2 ->
  trans_cmd ex_ids tmps optaddrb optaddre rm2 c = 
    Some (ex_ids', tmps', cs, optaddrb', optaddre') ->
  reg_simulation mi rm1 rm2 lc1 lc2 ->
  mem_simulation mi TD MM1 Mem1 Mem2 ->
  SoftBound.dbCmd TD gl lc1 rm1 als Mem1 MM1 c lc1' rm1' als' Mem1' MM1' tr r ->
  exists lc2', exists Mem2', exists mi',
    SimpleSE.dbCmds TD gl lc2 als Mem2 cs lc2' als' Mem2' tr /\
    reg_simulation mi' rm1' rm2 lc1' lc2' /\
    mem_simulation mi' TD MM1' Mem1' Mem2' /\
    Values.inject_incr mi mi'.
Proof.
  intros c TD lc1 rm1 als gl Mem1 MM1 lc1' als' Mem1' MM1' tr lc2 Mem2 rm2 rm1' 
    cs ex_ids tmps ex_ids' tmps' r optaddrb optaddre optaddrb' optaddre' mi
    Hnontemp Hnotin Htrans Hrsim Hmsim HdbCmd.
  (sb_dbCmd_cases (destruct HdbCmd) Case); try solve [inversion Hnontemp].

Case "dbBop".
  inv Htrans.
  eapply simulation__BOP in H; eauto.
  destruct H as [gv3' [H1 H2]].
  exists (updateAddAL GenericValue lc2 id0 gv3'). exists Mem2. exists mi.
  split.
   assert (trace_nil = trace_app trace_nil trace_nil) as EQ. auto.
   rewrite EQ.
   eapply SimpleSE.dbCmds_cons; eauto.
     apply SimpleSE.dbBop; auto.
  split; auto.
    apply reg_simulation__updateAddAL; auto.

admit. admit. admit.

Case "dbMalloc".
  eapply trans_cmd__is__correct__dbMalloc; eauto.

Case "dbMalloc_error".
  admit.    

Case "dbAlloca".
  admit. 

Case "dbAlloca_error".
  admit. 

Case "dbLoad_nptr".
  eapply trans_cmd__is__correct__dbLoad_nptr; eauto.

Case "dbLoad_ptr".
  simpl in Htrans.
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
SCase "t is ptr".
    remember (lookupAL (id * id) rm2 id0) as R5.
    destruct R5; try solve [inversion Htrans].
    destruct p as [bid0 eid0].
    destruct optaddrb as [addrb | ].
      destruct optaddre as [addre | ]; inv Htrans.

(* case 1 *)
  assert (J:=H1).
  unfold SoftBound.assert_mptr in J.
  case_eq (SoftBound.get_reg_metadata TD Mem0 gl rm vp).
  intros md_base md_bound J1.
  rewrite J1 in J.
  remember (GV2ptr TD (getPointerSize TD) gvp) as R.
  destruct R; try solve [inversion J].
  destruct v; try solve [inversion J].
  remember (GV2ptr TD (getPointerSize TD) md_base) as R1.
  destruct R1; try solve [inversion J].
  destruct v; try solve [inversion J].
  remember (GV2ptr TD (getPointerSize TD) md_bound) as R2.
  destruct R2; try solve [inversion J].
  destruct v; try solve [inversion J].
  remember (getTypeAllocSize TD t) as R3.
  destruct R3; try solve [inversion J].
  eapply simulation__getOperandValue in H0; eauto.
  destruct H0 as [gvp2 [H00 H01]].            
  unfold SoftBound.get_reg_metadata in J1.
  eapply simulation__mload in H2; eauto.
  destruct H2 as [gv2 [H21 H22]].
  destruct Hrsim as [Hrsim1 [Hrsim2 Hrsim3]].
  case_eq (SoftBound.get_mem_metadata TD MM gvp).
  intros mb_base0 md_bound0 JJ.
  unfold SoftBound.get_mem_metadata in JJ.

(*
  destruct vp as [pid |].
    SSCase "vp is value_id".
    remember (lookupAL SoftBound.metadata rm pid) as R4.
    destruct R4; subst.
      SSSCase "pid is in rm".
      symmetry in HeqR9.
      assert (HeqR9':=HeqR9).
      apply Hrsim2 in HeqR9'.      
      destruct HeqR9' as [bid [eid [bgv2 [egv2 [J1 [J2 [J3 [J4 J5]]]]]]]].
      exists 
       (updateAddAL _ 
        (updateAddAL _ 
          (updateAddAL _ 
           (updateAddAL GenericValue lc2 ptmp gvp2)
           btmp bgv2)
          etmp egv2)
        id0 gv2).
      exists Mem2. exists mi.
      split.
        SSSSCase "dbCmds".

    assert (trace_nil = trace_app trace_nil trace_nil) as EQ. auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with (lc2:=updateAddAL GenericValue lc2 ptmp gvp2)
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. simpl. simpl in H00.
        rewrite H00. auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) btmp bgv2)(als2:=als)
      (Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. 
        simpl in HeqR. rewrite J1 in HeqR. inv HeqR.
        simpl.
        rewrite <- lookupAL_updateAddAL_neq; auto.
          rewrite J2. auto.
          admit. (* fresh id *)
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2)
              btmp bgv2) etmp egv2)
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. 
        simpl in HeqR. rewrite J1 in HeqR. inv HeqR.
        simpl.
        rewrite <- lookupAL_updateAddAL_neq; auto.
          rewrite <- lookupAL_updateAddAL_neq; auto.
            rewrite J3. auto.
            admit. (* fresh id *)
          admit. (* fresh id *)
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) btmp bgv2)
        etmp egv2)
      (als2:=als)(Mem2:=Mem2); auto.
       clear - H00 J1 J2 J3 J4 J5 J H00 H01 HeqR0 HeqR5 HeqR6.
       admit. (* assert_mptr_fn' axiom. *)
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ 
        (updateAddAL _ lc2 ptmp gvp2) btmp bgv2) etmp egv2) id0 gv2)
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbLoad with (mp:=gvp2); auto.
        simpl.
        rewrite <- lookupAL_updateAddAL_neq; auto.
        rewrite <- lookupAL_updateAddAL_neq; auto.
        rewrite <- lookupAL_updateAddAL_neq; auto.
          admit. (* fresh id *)
          admit. (* fresh id *)
          admit. (* fresh id *)

      split; auto.
        SSSSCase "rsim".

    clear - Hrsim1 H22 subcase subsubcase subsubsubcase subsubsubsubcase.
    split.
          SSSSSCase "rsim1".
      intros i0 gv1 J.
      destruct (id_dec id0 i0); subst.
        rewrite lookupAL_updateAddAL_eq in J.
        inv J.
        exists gv2.
        split; auto.
          admit. (* i0 <> btmp etmp ptmp *)
 
        rewrite <- lookupAL_updateAddAL_neq in J; auto.
        apply Hrsim1 in J.
        destruct J as [gv2' [J J2]].
        exists gv2'.
        split; auto.
          admit. (* i0 <> bid eid tmp *)

          SSSSSCase "rsim2".
      admit. (* lets see if the proofs need this direction. *)

      SSSCase "pid isnt in rm".
      inv J1.
      eapply trans_cmd__is__correct__dbLoad_nptr__case in J; eauto.
      inversion J.

    SSCase "vp is value_const".
    remember (SoftBound.get_const_metadata c) as R.
    destruct R. 
      destruct p as [bc ec].
      remember (const2GV TD Mem0 gl bc) as R1.
      remember (const2GV TD Mem0 gl ec) as R2.
      destruct R1; simpl in J1.       
        destruct R2; simpl in J1.
          inv J1.
          simpl in HeqR.
          rewrite <- HeqR8 in HeqR.
          remember (Constant.getTyp c) as R3.
          destruct R3; inv HeqR.
          symmetry in HeqR10, HeqR9.
          assert (Hmject:=Hmsim).
          destruct Hmject as [Hmject _].
          apply sb_mem_inj__const2GV with (Mem':=Mem2)(mi:=mi) in HeqR10; auto.
          apply sb_mem_inj__const2GV with (Mem':=Mem2)(mi:=mi) in HeqR9; auto.
          destruct HeqR10 as [mb_bound' [HeqR100 HeqR101]].            
          destruct HeqR9 as [mb_base' [HeqR90 HeqR91]].           
          exists 
           (updateAddAL _ 
            (updateAddAL _ 
             (updateAddAL _ 
              (updateAddAL GenericValue lc2 ptmp gvp2)
              btmp mb_base')
             etmp mb_bound')
            id0 gv2).
           exists Mem2. exists mi.
           split.
           SSSCase "dbCmds".

    assert (trace_nil = trace_app trace_nil trace_nil) as EQ. auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with (lc2:=updateAddAL GenericValue lc2 ptmp gvp2)
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. simpl. simpl in H00.
        rewrite H00. auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) btmp mb_base')(als2:=als)
      (Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. simpl. rewrite HeqR90.
        clear - HeqR8 HeqR11.
        admit. (* given wf typ, t0 must be of ptr. *)
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2)
              btmp mb_base') etmp mb_bound')
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbCast; auto.
        unfold CAST. simpl. rewrite HeqR100.
        clear - HeqR8 HeqR11.
        admit. (* given wf typ, t0 must be of ptr. *)
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ lc2 ptmp gvp2) btmp 
        mb_base') etmp mb_bound') (als2:=als)(Mem2:=Mem2); auto.
       clear - J HeqR0 HeqR5 HeqR6 H00 H00 H01 HeqR100 HeqR101 HeqR90 HeqR91.
       admit. (* assert_mptr_fn' axiom. *)
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _ (updateAddAL _ (updateAddAL _ 
        (updateAddAL _ lc2 ptmp gvp2) btmp mb_base') etmp mb_bound') id0 gv2)
      (als2:=als)(Mem2:=Mem2); auto.
      apply SimpleSE.dbLoad with (mp:=gvp2); auto.

           split; auto.
        SSSCase "rsim".

    clear - Hrsim1 H22 subcase subsubcase subsubsubcase.
    split.
          SSSSSCase "rsim1".
      intros i0 gv1 J.
      destruct (id_dec id0 i0); subst.
        rewrite lookupAL_updateAddAL_eq in J.
        inv J.
        exists gv2.
        split; auto.
          admit. (* i0 <> btmp etmp ptmp *)
 
        rewrite <- lookupAL_updateAddAL_neq in J; auto.        
        apply Hrsim1 in J.
        destruct J as [gv2' [J J2]].
        exists gv2'.
        split; auto.
          admit. (* i0 <> bid eid tmp *)

          SSSSSCase "rsim2".
      admit. (* lets see if the proofs need this direction. *)

          inv J1.
          eapply trans_cmd__is__correct__dbLoad_nptr__case in J; eauto.
          inversion J.

        inv J1.
        eapply trans_cmd__is__correct__dbLoad_nptr__case in J; eauto.
        inversion J.
        
      inv J1.
      eapply trans_cmd__is__correct__dbLoad_nptr__case in J; eauto.
      inversion J.

    admit.
*)
       admit.

(* case 2 *)
      destruct optaddre as [addre | ]; inv Htrans.
        admit.

SCase "t isnt ptr".
    unfold isPointerTyp in H3.
    rewrite <- HeqR4 in H3.
    inversion H3.

admit. admit. admit.

Case "dbLoad_abort".
  simpl in Htrans.
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
  simpl in Htrans.
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
  simpl in Htrans.
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
  simpl in Htrans.
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
    optaddrb optaddre optaddrb' optaddre' mi, 
  non_temporal_cmds cs ->
  AtomSetImpl.inter (getCmdsIDs cs) (codom rm2) [<=] empty ->
  trans_cmds ex_ids tmps optaddrb optaddre rm2 cs = 
    Some (ex_ids', tmps', cs', optaddrb', optaddre') ->
  reg_simulation mi rm1 rm2 lc1 lc2 ->
  mem_simulation mi TD MM1 Mem1 Mem2 ->
  SoftBound.dbCmds TD gl lc1 rm1 als Mem1 MM1 cs lc1' rm1' als' Mem1' MM1' tr r 
    ->
  exists lc2', exists Mem2', exists mi',
    SimpleSE.dbCmds TD gl lc2 als Mem2 cs' lc2' als' Mem2' tr /\
    reg_simulation mi' rm1' rm2 lc1' lc2' /\
    mem_simulation mi' TD MM1' Mem1' Mem2' /\
    Values.inject_incr mi mi'.
Admitted.

End SBpass.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)
