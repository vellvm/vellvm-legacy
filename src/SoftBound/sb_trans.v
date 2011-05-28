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

Fixpoint gen_metadata_cmds nts (ex_ids:ids) (rm:rmap) (cs:cmds) 
  : option(ids*rmap) :=
match cs with
| nil => Some (ex_ids,rm)
| c::cs' => 
   do t <- getCmdTyp nts c;
   if isPointerTypB t then
     let id0 := getCmdID c in
     let '(_,_,ex_ids',rm') := gen_metadata_id ex_ids rm id0 in
     gen_metadata_cmds nts ex_ids' rm' cs'
   else gen_metadata_cmds nts ex_ids rm cs'
end.

Fixpoint gen_metadata_phinodes (ex_ids:ids) (rm:rmap) (ps:phinodes) : ids*rmap :=
match ps with
| nil => (ex_ids,rm)
| p::ps' => 
   let t := getPhiNodeTyp p in
   if isPointerTypB t then
     let id0 := getPhiNodeID p in
     let '(_,_,ex_ids',rm') := gen_metadata_id ex_ids rm id0 in
     gen_metadata_phinodes ex_ids' rm' ps'
   else gen_metadata_phinodes ex_ids rm ps'
end.

Definition gen_metadata_block nts (ex_ids:ids) (rm:rmap) (b:block) 
  : option(ids*rmap) :=
let '(block_intro _ ps cs _) := b in
let '(ex_ids', rm') := gen_metadata_phinodes ex_ids rm ps in
gen_metadata_cmds nts ex_ids' rm' cs.

Fixpoint gen_metadata_blocks nts (ex_ids:ids) (rm:rmap) (bs:blocks) 
  : option(ids*rmap) :=
match bs with
| nil => Some (ex_ids,rm)
| b::bs' => 
    match gen_metadata_block nts ex_ids rm b with
    | Some (ex_ids',rm') => gen_metadata_blocks nts ex_ids' rm' bs'
    | None => None
    end
end.

Fixpoint gen_metadata_args (ex_ids:ids) (rm:rmap) (la:args) : ids*rmap :=
match la with
| nil => (ex_ids,rm)
| (t,id0)::la' => 
   if isPointerTypB t then
     let '(_,_,ex_ids',rm') := gen_metadata_id ex_ids rm id0 in
     gen_metadata_args ex_ids' rm' la'
   else gen_metadata_args ex_ids rm la'
end.

Definition gen_metadata_fdef nts (ex_ids:ids) (rm:rmap) (f:fdef) 
  : option(ids*rmap) :=
let '(fdef_intro (fheader_intro _ _ la) bs) := f in
let '(ex_ids', rm') := gen_metadata_args ex_ids rm la in
gen_metadata_blocks nts ex_ids' rm' bs.

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

Definition type_size t :=
  value_const
    (const_castop 
      castop_ptrtoint 
      (const_gep false 
        (const_null t) 
        (Cons_list_const int1 Nil_list_const))
      (typ_int Size.ThirtyTwo)
    ).

Definition trans_nbranch (ex_ids tmps:ids) (optaddrb optaddre:option id)
  (rm:rmap) (nb:nbranch) : option (ids*ids*cmds*option id*option id) :=
let '(mkNB c notcall) := nb in
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

| _ => Some (ex_ids, tmps, [c], optaddrb, optaddre)
end.

Fixpoint trans_nbranchs (ex_ids tmps:ids) (optaddrb optaddre:option id) 
  (rm:rmap) (nbs:list nbranch) : option (ids*ids*cmds*option id*option id) :=
match nbs with
| nil => Some (ex_ids, tmps, nil, optaddrb, optaddre)
| nb::nbs' =>
    match (trans_nbranch ex_ids tmps optaddrb optaddre rm nb) with
    | Some (ex_ids1, tmps1, cs1, optaddrb, optaddre) =>
        match (trans_nbranchs ex_ids1 tmps1 optaddrb optaddre rm nbs') with
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

Axiom isSysLib : id -> bool.

Axiom rename_fid : id -> id.

Definition trans_call_aux
(ex_ids : ids) (tmps : ids) (optaddrb : monad id) (optaddre : monad id) 
(rm : rmap) (i0 : id) (n : noret) (t : tailc) (t0 : typ) (v : value)
(p : params) : option (ids*ids*cmds*option id*option id) :=
match
  (match v with
   | value_const (const_gid _ fid) =>
       if isSysLib fid then
          Some (ex_ids, tmps, nil, nil)
       else trans_params ex_ids tmps rm p
   | _ => trans_params ex_ids tmps rm p
  end) with
| Some (ex_ids', tmps', cs, p') =>
        Some (ex_ids', tmps', cs++[insn_call i0 n t t0 v (p++p')],
              optaddrb, optaddre)
| None => None
end.

Definition trans_call : forall (ex_ids tmps:ids) (optaddrb optaddre:option id)
  (rm:rmap) (c:cmd) (iscall:isCall c = true),
   option (ids*ids*cmds*option id*option id).
Proof.
  intros. unfold isCall in iscall.
  destruct c; try solve [inversion iscall].
  apply (trans_call_aux ex_ids tmps optaddrb optaddre rm i0 n t t0 v p).
Qed.

Definition trans_subblock (ex_ids tmps:ids) (optaddrb optaddre:option id) 
  (rm:rmap) (sb:subblock) : option (ids*ids*option id*option id*cmds) :=
let '(mkSB nbs call0 iscall0) := sb in
match trans_nbranchs ex_ids tmps optaddrb optaddre rm nbs with
| Some (ex_ids',tmps',cs1,optaddrb,optaddre) => 
    match trans_call ex_ids' tmps' optaddrb optaddre rm call0 iscall0 with
    | Some (ex_ids'',tmps'',cs2,optaddrb,optaddre) =>
        Some (ex_ids'',tmps'',optaddrb,optaddre,cs1++cs2)
    | None => None
    end
| None => None
end.

Fixpoint trans_subblocks (ex_ids tmps:ids) (optaddrb optaddre:option id) 
  (rm:rmap) (sbs:list subblock) : option (ids*ids*option id*option id*cmds) :=
match sbs with
| nil => Some (ex_ids, tmps, optaddrb, optaddre, nil)
| sb::sbs' =>
    match (trans_subblock ex_ids tmps optaddrb optaddre rm sb) with
    | Some (ex_ids1, tmps1, optaddrb, optaddre, cs1) =>
        match (trans_subblocks ex_ids1 tmps1 optaddrb optaddre rm sbs') with
        | Some (ex_ids2, tmps2, optaddrb, optaddre, cs2) => 
            Some (ex_ids2, tmps2, optaddrb, optaddre, cs1++cs2)
        | _ => None
        end
    | _ => None
    end
end.

Definition trans_block (ex_ids tmps:ids) (optaddrb optaddre:option id) (rm:rmap)
  (b:block) : option (ids*ids*option id*option id*block) :=
let '(block_intro l1 ps1 cs1 tmn1) := b in
let '(sbs1, nbs1) := (cmds2sbs cs1) in
match trans_phinodes rm ps1 with
| None => None
| Some ps2 => 
    match trans_subblocks ex_ids tmps optaddrb optaddre rm sbs1 with
    | Some (ex_ids',tmps',optaddrb,optaddre,cs1) => 
        match trans_nbranchs ex_ids' tmps' optaddrb optaddre rm nbs1 with
        | Some (ex_ids'',tmps'',cs2,optaddrb,optaddre) =>
            Some (ex_ids'',tmps'',optaddrb,optaddre, 
                   block_intro l1 ps2 (cs1++cs2) tmn1)
        | None => None
        end
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

Definition trans_fdef nts (f:fdef) : option fdef :=
let '(fdef_intro (fheader_intro t fid la) bs) := f in
if SimpleSE.isCallLib fid then Some f
else
  let ex_ids := getFdefIDs f in
  match gen_metadata_fdef nts ex_ids nil f with
  | Some (ex_ids,rm) =>
      match (trans_args rm la) with
      | Some la' =>
          match (trans_blocks ex_ids nil None None rm bs) with
          | Some (ex_ids, tmps, optaddrb, optaddre, b'::bs') => 
              Some (fdef_intro 
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
    | Some f' => Some (product_fdef f')
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

Definition meminj_no_overlap (f: meminj) (m: mem) : Prop :=
  forall b1 b1' delta1 b2 b2' delta2,
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2'.

Lemma meminj_no_overlap__implies : forall f m,
  meminj_no_overlap f m -> Mem.meminj_no_overlap f m.
Proof.
  intros f m J.
  unfold meminj_no_overlap in J.
  unfold Mem.meminj_no_overlap.
  eauto.
Qed.

Record wf_sb_mi maxb mi Mem1 Mem2 := mk_wf_sb_mi {
  Hno_overlap : meminj_no_overlap mi Mem1;
  Hnull : mi Mem.nullptr = Some (Mem.nullptr, 0);
  Hmap1 : forall b, b >= Mem.nextblock Mem1 -> mi b = None;
  Hmap2 : forall b1 b2 delta2, 
    mi b1 = Some (b2, delta2) -> b2 < Mem.nextblock Mem2;
  mi_freeblocks: forall b, ~(Mem.valid_block Mem1 b) -> mi b = None;
  mi_mappedblocks: forall b b' delta, 
    mi b = Some(b', delta) -> Mem.valid_block Mem2 b';
  mi_range_block: forall b b' delta, 
    mi b = Some(b', delta) -> delta = 0;
  mi_bounds: forall b b' delta, 
    mi b = Some(b', delta) -> Mem.bounds Mem1 b = Mem.bounds Mem2 b';
  mi_globals : forall b, b <= maxb -> mi b = Some (b, 0)
  }.

Definition gv_inject (mi: Values.meminj) (gv gv':GenericValue) : Prop :=
let '(vals,mks) := List.split gv in 
let '(vals',mks') := List.split gv' in 
val_list_inject mi vals vals' /\ mks = mks'.

Definition reg_simulation (mi:Values.meminj) TD gl (rm1:SoftBound.rmetadata) 
  (rm2:rmap) Mem1 Mem2 (lc1 lc2:GVMap) : Prop :=
(forall i0 gv1, 
  lookupAL _ lc1 i0 = Some gv1 -> 
  exists gv2, 
    lookupAL _ lc2 i0 = Some gv2 /\ gv_inject mi gv1 gv2
) /\
(forall vp bgv1 egv1, 
  SoftBound.get_reg_metadata TD Mem1 gl rm1 vp = 
    Some (SoftBound.mkMD bgv1 egv1) -> 
  exists t2, exists bv2, exists ev2, exists bgv2, exists egv2,
    get_reg_metadata rm2 vp = Some (t2, bv2, ev2) /\
    getOperandValue TD Mem2 bv2 lc2 gl = Some bgv2 /\
    getOperandValue TD Mem2 ev2 lc2 gl = Some egv2 /\
    gv_inject mi bgv1 bgv2 /\
    gv_inject mi egv1 egv2
).

Fixpoint wf_const (c:const) : Prop :=
match c with
| const_zeroinitializer _ | const_int _ _ | const_floatpoint _ _ 
| const_undef _ | const_null _ | const_gid _ _ => True
| const_arr _ cs | const_struct cs => wf_consts cs
| const_truncop _ c1 _ | const_extop _ c1 _ => wf_const c1
| const_extractvalue c cs | const_gep _ c cs => wf_const c /\ wf_consts cs
| const_select c1 c2 c3 => wf_const c1 /\ wf_const c2 /\ wf_const c3
| const_icmp _ c1 c2 | const_fcmp _ c1 c2 | const_bop _ c1 c2 
| const_fbop _ c1 c2 => wf_const c1 /\ wf_const c2
| const_castop cop c _ => cop <> castop_inttoptr /\ wf_const c
| const_insertvalue c1 c2 cs => wf_const c1 /\ wf_const c2 /\ wf_consts cs
end
with wf_consts (cs:list_const) : Prop :=
match cs with
| Nil_list_const => True
| Cons_list_const c cs => wf_const c /\ wf_consts cs
end.

Fixpoint wf_global (maxb:Values.block) (gv:GenericValue) 
  : Prop :=
match gv with
| nil => True
| (Vptr b _,_)::gv' => b <= maxb /\ wf_global maxb gv'
| _::gv' => wf_global maxb gv'
end.

Fixpoint wf_globals maxb (gl:GVMap) : Prop :=
match gl with
| nil => True
| (_,gv)::gl' => wf_global maxb gv /\ wf_globals maxb gl'
end.

Definition wf_value v : Prop :=
match v with
| value_const c => wf_const c
| _ => True
end.

Definition mem_simulation (mi:Values.meminj) TD (max_gblock:Values.block) 
  (MM1:SoftBound.mmetadata) (Mem1 Mem2:mem) : Prop :=
Mem.mem_inj mi Mem1 Mem2 /\
0 <= max_gblock < Mem.nextblock Mem2 /\
(forall lc2 gl b ofs bgv egv als addrb addre bid0 eid0 v pgv',  
  wf_value v -> wf_globals max_gblock gl -> 
  SoftBound.get_mem_metadata TD MM1 (ptr2GV TD (Vptr b ofs)) = 
    SoftBound.mkMD bgv egv -> 
  gv_inject mi (ptr2GV TD (Vptr b ofs)) pgv' ->
  getOperandValue TD Mem2 v lc2 gl = Some pgv' ->
  exists bgv', exists egv', exists Mem2',
  SimpleSE.dbCmds TD gl lc2 als Mem2
    (insn_call fake_id true false typ_void get_mmetadata_fn 
       ((p8,v)::
        (p8,(value_id addrb))::
        (p8,(value_id addre))::nil)::
     insn_load bid0 p8 (value_id addrb) Align.Zero::
     insn_load eid0 p8 (value_id addre) Align.Zero::   
     nil) (updateAddAL _ (updateAddAL _ lc2 bid0 bgv') eid0 egv') als Mem2' 
     trace_nil /\
    gv_inject mi bgv bgv' /\
    gv_inject mi egv egv' /\
    Mem.mem_inj Memdata.inject_id Mem2 Mem2'
).

Fixpoint codom (rm:rmap) : atoms :=
match rm with
| nil => empty
| (_,(bid,eid))::rm' => singleton bid `union` singleton eid `union` codom rm'
end.


Definition veq Mem (v1 v2:val) : bool :=
match v1, v2 with
| Vundef, Vundef => true
| Vundef, _ => false
| _, Vundef => false
| Vint wz1 i1, Vint wz2 i2 => zeq (Int.unsigned wz1 i1) (Int.unsigned wz2 i2)
| Vint wz1 i1, Vfloat f2 => 
    zeq (Int.unsigned wz1 i1) (Int.unsigned 31 (Floats.Float.intuoffloat f2))
| Vfloat f1, Vint wz2 i2 => 
    zeq (Int.unsigned 31 (Floats.Float.intuoffloat f1)) (Int.unsigned wz2 i2)
| Vfloat f1, Vfloat f2 => match (Floats.Float.eq_dec f1 f2) with
                          | left _ => true
                          | right _ => false
                          end
| Vptr b1 o1, Vptr b2 o2 => eq_block b1 b2 && 
                            zeq (Int.unsigned 31 o1) (Int.unsigned 31 o2)
| Vinttoptr i1, Vinttoptr i2 => 
    (* FIXME: Should we compare Vinttoptr and Vptr? *)
    zeq (Int.unsigned 31 i1) (Int.unsigned 31 i2)
| Vptr b1 o1, Vinttoptr i2 =>
    match Mem.ptr2int Mem b1 0 with
    | ret z => zeq (z + Int.signed 31 o1) (Int.unsigned 31 i2)
    | merror => false
    end
| Vinttoptr i1, Vptr b2 o2 =>
    match Mem.ptr2int Mem b2 0 with
    | ret z => zeq (z + Int.signed 31 o2) (Int.unsigned 31 i1)
    | merror => false
    end
| _, _ => false
end.

Fixpoint gveq Mem (gv1 gv2:GenericValue) : bool :=
match gv1, gv2 with
| nil, nil => true
| (v1,c1)::gv1', (v2,c2)::gv2' => veq Mem v1 v2 && 
                                  AST.memory_chunk_eq c1 c2 && 
                                  gveq Mem gv1' gv2'
| _, _ => false
end.

Axiom get_mmetadata_fn__alloc : forall
  (TD : TargetData)
  (Mem2 : Mem.mem_)
  (Mem2' : Mem.mem_)
  (mb2 : Values.block)
  lo hi
  (HeqR2 : (Mem2', mb2) = Mem.alloc Mem2 lo hi)
  (lc2 : GVMap)
  (gl : GVMap)
  (als : list mblock)
  (addrb0 : id)
  (addre0 : id)
  (bid0 : id)
  (eid0 : id)
  (v : value)
  (bgv' : GenericValue)
  (egv' : GenericValue)
  (Mem21 : mem)
  (J37 : dbCmds TD gl lc2 als Mem2
          (insn_call fake_id true false typ_void get_mmetadata_fn
             ((p8, v)
              :: (p8, value_id addrb0) :: (p8, value_id addre0) :: nil)
           :: insn_load bid0 p8 (value_id addrb0) Align.Zero
              :: insn_load eid0 p8 (value_id addre0) Align.Zero :: nil)
          (updateAddAL GenericValue (updateAddAL GenericValue lc2 bid0 bgv')
             eid0 egv') als Mem21 trace_nil),
   exists Mem21' : mem,
     dbCmds TD gl lc2 als Mem2'
       (insn_call fake_id true false typ_void get_mmetadata_fn
          ((p8, v) :: (p8, value_id addrb0) :: (p8, value_id addre0) :: nil)
        :: insn_load bid0 p8 (value_id addrb0) Align.Zero
           :: insn_load eid0 p8 (value_id addre0) Align.Zero :: nil)
       (updateAddAL GenericValue (updateAddAL GenericValue lc2 bid0 bgv')
          eid0 egv') als Mem21' trace_nil /\
     Mem.mem_inj inject_id Mem2' Mem21'.

Axiom assert_mptr_fn__ok : forall 
  (lc2 : GVMap)
  (Mem2 : mem)
  (mi : meminj)
  (t : typ)
  (vp : value)
  (ptmp : id)
  (btmp : id)
  (etmp : id)
  (TD : TargetData)
  (gl : GVMap)
  (als : list mblock)
  (gvp : GenericValue)
  (md_base : GenericValue)
  (md_bound : GenericValue)
  (b : Values.block)
  (i0 : int32)
  (HeqR0 : ret Vptr b i0 = GV2ptr TD (getPointerSize TD) gvp)
  (b0 : Values.block)
  (i1 : int32)
  (HeqR5 : ret Vptr b0 i1 = GV2ptr TD (getPointerSize TD) md_base)
  (b1 : Values.block)
  (i2 : int32)
  (HeqR6 : ret Vptr b1 i2 = GV2ptr TD (getPointerSize TD) md_bound)
  (s : sz)
  (HeqR7 : ret s = getTypeAllocSize TD t)
  (J : zeq b b0 && zeq b0 b1 && zle (Int.signed 31 i1) (Int.signed 31 i0) &&
      zle (Int.signed 31 i0 + Size.to_Z s) (Int.signed 31 i2))
  (gvp2 : GenericValue)
  (H00 : getOperandValue TD Mem2 vp lc2 gl = ret gvp2)
  (H01 : gv_inject mi gvp gvp2)
  (bv2 : value)
  (ev2 : value)
  (bgv2 : GenericValue)
  (egv2 : GenericValue)
  (J2 : getOperandValue TD Mem2 bv2 lc2 gl = ret bgv2)
  (J3 : getOperandValue TD Mem2 ev2 lc2 gl = ret egv2)
  (J4 : gv_inject mi md_base bgv2)
  (J5 : gv_inject mi md_bound egv2),
   dbCmd TD gl
     (updateAddAL GenericValue
        (updateAddAL GenericValue (updateAddAL GenericValue lc2 ptmp gvp2)
           btmp bgv2) etmp egv2) als Mem2
     (insn_call fake_id true false typ_void assert_mptr_fn
        ((p8, value_id ptmp)
         :: (p8, value_id btmp)
            :: (p8, value_id etmp)
               :: (i32, type_size t) :: (i32, vint1) :: nil))
     (updateAddAL GenericValue
        (updateAddAL GenericValue (updateAddAL GenericValue lc2 ptmp gvp2)
           btmp bgv2) etmp egv2) als Mem2 trace_nil.

Axiom get_mmetadata_fn__weaken : forall
  (lc2 : GVMap)
  (Mem2 : mem)
  (addrb : id)
  (addre : id)
  (id0 : atom)
  (vp : value)
  (ptmp : id)
  (btmp : id)
  (etmp : id)
  (bid0 : id)
  (eid0 : id)
  (TD : TargetData)
  (gl : GVMap)
  (als : list mblock)
  (gvp2 : GenericValue)
  (H00 : getOperandValue TD Mem2 vp lc2 gl = ret gvp2)
  (gv2 : GenericValue)
  (bgv' : GenericValue)
  (egv' : GenericValue)
  (Mem2' : mem)
  (JJ1 : dbCmds TD gl lc2 als Mem2
          (insn_call fake_id true false typ_void get_mmetadata_fn
             ((p8, vp) :: (p8, value_id addrb) :: (p8, value_id addre) :: nil)
           :: insn_load bid0 p8 (value_id addrb) Align.Zero
              :: insn_load eid0 p8 (value_id addre) Align.Zero :: nil)
          (updateAddAL GenericValue (updateAddAL GenericValue lc2 bid0 bgv')
             eid0 egv') als Mem2' trace_nil)
  (bgv2 : GenericValue)
  (egv2 : GenericValue),
   dbCmds TD gl
     (updateAddAL GenericValue
        (updateAddAL GenericValue
           (updateAddAL GenericValue (updateAddAL GenericValue lc2 ptmp gvp2)
              btmp bgv2) etmp egv2) id0 gv2) als Mem2
     (insn_call fake_id true false typ_void get_mmetadata_fn
        ((p8, value_id ptmp)
         :: (pp8, value_id addrb)
            :: (pp8, value_id addre)
               :: (p8, vnullp8) :: (i32, vint1) :: (p32, vnullp32) :: nil)
      :: insn_load bid0 p8 (value_id addrb) Align.Zero
         :: insn_load eid0 p8 (value_id addre) Align.Zero :: nil)
     (updateAddAL GenericValue
        (updateAddAL GenericValue
           (updateAddAL GenericValue
              (updateAddAL GenericValue
                 (updateAddAL GenericValue
                    (updateAddAL GenericValue lc2 ptmp gvp2) btmp bgv2) etmp
                 egv2) id0 gv2) bid0 bgv') eid0 egv') als Mem2 trace_nil.

Axiom get_mmetadata_fn__prop : forall m Mem2 b2 ofs2 v1 Mem2' lc2 gl als addrb
    addre bid0 eid0 bgv' egv' Mem3 TD v,
  Mem.store m Mem2 b2 ofs2 v = ret Mem2' ->
  dbCmds TD gl lc2 als Mem2
         (insn_call fake_id true false typ_void get_mmetadata_fn
            ((p8, v1) :: (p8, value_id addrb) :: (p8, value_id addre) :: nil)
          :: insn_load bid0 p8 (value_id addrb) Align.Zero
             :: insn_load eid0 p8 (value_id addre) Align.Zero :: nil)
         (updateAddAL GenericValue (updateAddAL GenericValue lc2 bid0 bgv')
            eid0 egv') als Mem3 trace_nil ->
   exists Mem2'0 : mem,
     dbCmds TD gl lc2 als Mem2'
       (insn_call fake_id true false typ_void get_mmetadata_fn
          ((p8, v1) :: (p8, value_id addrb) :: (p8, value_id addre) :: nil)
        :: insn_load bid0 p8 (value_id addrb) Align.Zero
           :: insn_load eid0 p8 (value_id addre) Align.Zero :: nil)
       (updateAddAL GenericValue (updateAddAL GenericValue lc2 bid0 bgv')
          eid0 egv') als Mem2'0 trace_nil /\
     Mem.mem_inj inject_id Mem2' Mem2'0.

Axiom set_mmetadata_fn__prop : forall TD gl lc2 als Mem2 ptmp pgv' bv0 ev0,
  lookupAL _ lc2 ptmp = Some pgv' ->
  exists Mem2',
    SimpleSE.dbCmd TD gl lc2 als Mem2
      (insn_call fake_id true false typ_void set_mmetadata_fn
        ((p8, value_id ptmp) :: (p8, bv0) :: (p8, ev0) :: (p8, vnullp8) :: 
         (i32, vint1) :: (i32, vint1) :: nil)) 
      lc2 als Mem2' trace_nil /\
    Mem.mem_inj Memdata.inject_id Mem2 Mem2' /\
    Mem.nextblock Mem2 <= Mem.nextblock Mem2'.

Axiom set_mmetadata_fn__getOperandValue : forall
  (lc2 : AssocList GenericValue)
  (gl : GVMap)
  (als : list mblock)
  (ptmp : atom)
  (bv0 : value)
  (ev0 : value)
  (Mem2 : mem)
  (TD : TargetData)
  (Mem2' : mem)
  (J : dbCmd TD gl lc2 als Mem2
        (insn_call fake_id true false typ_void set_mmetadata_fn
           ((p8, value_id ptmp)
            :: (p8, bv0)
               :: (p8, ev0)
                  :: (p8, vnullp8) :: (i32, vint1) :: (i32, vint1) :: nil))
        lc2 als Mem2' trace_nil)
  (lc0 : GVMap)
  (gl0 : GVMap)
  (v0 : value),
  getOperandValue TD Mem2' v0 lc0 gl0 = getOperandValue TD Mem2 v0 lc0 gl0.

Axiom get_set_mmetadata_fn : forall
  (lc2 : AssocList GenericValue)
  (gl : GVMap)
  (b : Values.block)
  (als : list mblock)
  (pgv' : GenericValue)
  (bgv' : GenericValue)
  (egv' : GenericValue)
  (mi : meminj)
  (ptmp : atom)
  (bv0 : value)
  (ev0 : value)
  (Mem2 : mem)
  (TD : TargetData)
  (Hlookup : lookupAL GenericValue lc2 ptmp = ret pgv')
  (Hgetb : getOperandValue TD Mem2 bv0 lc2 gl = ret bgv')
  (Hgete : getOperandValue TD Mem2 ev0 lc2 gl = ret egv')
  (Mem2' : mem)
  (J : dbCmd TD gl lc2 als Mem2
        (insn_call fake_id true false typ_void set_mmetadata_fn
           ((p8, value_id ptmp)
            :: (p8, bv0)
               :: (p8, ev0)
                  :: (p8, vnullp8) :: (i32, vint1) :: (i32, vint1) :: nil))
        lc2 als Mem2' trace_nil)
  (lc0 : GVMap)
  (gl0 : GVMap)
  (ofs0 : int32)
  (bgv0 : GenericValue)
  (egv0 : GenericValue)
  (als0 : list mblock)
  (addrb : id)
  (addre : id)
  (bid0 : id)
  (eid0 : id)
  (v0 : value)
  (pgv'0 : GenericValue)
  (J3 : getOperandValue TD Mem2' v0 lc0 gl0 = ret pgv'0)
  (J2 : gv_inject mi (ptr2GV TD (Vptr b ofs0)) pgv'0)
  (Hinjp : gv_inject mi (ptr2GV TD (Vptr b ofs0)) pgv'),
  exists Mem2'0 : mem,
     dbCmds TD gl0 lc0 als0 Mem2'
       (insn_call fake_id true false typ_void get_mmetadata_fn
          ((p8, v0) :: (p8, value_id addrb) :: (p8, value_id addre) :: nil)
        :: insn_load bid0 p8 (value_id addrb) Align.Zero
           :: insn_load eid0 p8 (value_id addre) Align.Zero :: nil)
       (updateAddAL GenericValue (updateAddAL GenericValue lc0 bid0 bgv')
          eid0 egv') als0 Mem2'0 trace_nil /\
     Mem.mem_inj inject_id Mem2' Mem2'0.

Axiom set_mmetadata_fn__prop' : forall TD gl lc1 Mem1 args lc2 als Mem2,
  dbCmd TD gl lc1 als Mem1 
    (insn_call fake_id true false typ_void set_mmetadata_fn args)
    lc2 als Mem2 trace_nil ->
  Mem.nextblock Mem1 <= Mem.nextblock Mem2 /\
  (forall b2, Mem.valid_block Mem1 b2 -> Mem.valid_block Mem2 b2) /\
  (forall b0, Mem.bounds Mem1 b0 = Mem.bounds Mem2 b0).

Axiom get_mmetadata_fn__prop' : forall Mem2 b lo hi v1 Mem2' lc2 gl als addrb
    addre bid0 eid0 bgv' egv' Mem3 TD,
  Mem.free Mem2 b lo hi = ret Mem2' ->
  dbCmds TD gl lc2 als Mem2
         (insn_call fake_id true false typ_void get_mmetadata_fn
            ((p8, v1) :: (p8, value_id addrb) :: (p8, value_id addre) :: nil)
          :: insn_load bid0 p8 (value_id addrb) Align.Zero
             :: insn_load eid0 p8 (value_id addre) Align.Zero :: nil)
         (updateAddAL GenericValue (updateAddAL GenericValue lc2 bid0 bgv')
            eid0 egv') als Mem3 trace_nil ->
   exists Mem2'0 : mem,
     dbCmds TD gl lc2 als Mem2'
       (insn_call fake_id true false typ_void get_mmetadata_fn
          ((p8, v1) :: (p8, value_id addrb) :: (p8, value_id addre) :: nil)
        :: insn_load bid0 p8 (value_id addrb) Align.Zero
           :: insn_load eid0 p8 (value_id addre) Align.Zero :: nil)
       (updateAddAL GenericValue (updateAddAL GenericValue lc2 bid0 bgv')
          eid0 egv') als Mem2'0 trace_nil /\
     Mem.mem_inj inject_id Mem2' Mem2'0.

Definition wf_cmd c : Prop :=
match c with
| insn_malloc _ _ v _ => wf_value v 
| insn_load _ _ vp _ => wf_value vp
| insn_store _ _ vp _ _ => wf_value vp
| _ => True
end.

Fixpoint wf_cmds cs : Prop :=
match cs with
| nil => True
| c::cs' => wf_cmd c /\ wf_cmds cs'
end.

Definition getValueID (v:value) : atoms :=
match v with
| value_id id => {{id}}
| value_const (const_gid _ id) => {{id}}
| value_const _ => {}
end.

Fixpoint getParamsOperand (lp:params) : atoms :=
match lp with
| nil => {}
  | (t, v)::lp' => getValueID v `union` (getParamsOperand lp')
end.

Definition getCmdOperands (i:cmd) : atoms :=
match i with
| insn_bop _ _ _ v1 v2 => getValueID v1 `union` getValueID v2
| insn_fbop _ _ _ v1 v2 => getValueID v1 `union` getValueID v2
(* | insn_extractelement _ _ v _ => getValueID v
| insn_insertelement _ _ v1 _ v2 _ => getValueID v1 `union` getValueID v2
*)
| insn_extractvalue _ _ v _ => getValueID v
| insn_insertvalue _ _ v1 _ v2 _ => getValueID v1 `union` getValueID v2
| insn_malloc _ _ v _ => getValueID v
| insn_free _ _ v => getValueID v
| insn_alloca _ _ v _ => getValueID v
| insn_load _ _ v _ => getValueID v
| insn_store _ _ v1 v2 _ => getValueID v1 `union` getValueID v2
| insn_gep _ _ _ v _ => getValueID v
| insn_trunc _ _ _ v _ => getValueID v
| insn_ext _ _ _ v1 typ2 => getValueID v1
| insn_cast _ _ _ v _ => getValueID v
| insn_icmp _ _ _ v1 v2 => getValueID v1 `union` getValueID v2
| insn_fcmp _ _ _ v1 v2 => getValueID v1 `union` getValueID v2
| insn_select _ v0 _ v1 v2 => 
    getValueID v0 `union` getValueID v1 `union` getValueID v2
| insn_call _ _ _ _ v0 lp => getValueID v0 `union` getParamsOperand lp
end.

Definition getCmdIDs (c:cmd) := {{getCmdID c}} `union` getCmdOperands c.

Definition id_fresh_in_value v1 i2 : Prop :=
match v1 with
| value_id i1 => i1 <> i2
| _ => True
end.

Fixpoint ids2atoms (ids0:ids) : atoms :=
match ids0 with
| nil => {}
| id0::ids0' => {{id0}} `union` ids2atoms ids0'
end.

Fixpoint rm_codom_disjoint (rm:rmap) : Prop :=
match rm with
| nil => True
| (id0,(bid,eid))::rm' => 
    id0 <> bid /\ id0 <> eid /\ bid <> eid /\ 
    id0 `notin` dom rm' `union` codom rm' /\
    bid `notin` dom rm' `union` codom rm' /\
    eid `notin` dom rm' `union` codom rm' /\
    rm_codom_disjoint rm' 
end.

Definition wf_fresh ex_ids c rm : Prop :=
AtomSetImpl.inter (getCmdIDs c) (codom rm) [<=] {} /\
getCmdID c `notin` getCmdOperands c /\
(getCmdIDs c) `union` codom rm [<=] ids2atoms ex_ids /\
rm_codom_disjoint rm.


Fixpoint wf_freshs ex_ids cs rm2 : Prop :=
match cs with
| nil => True
| c::cs' => wf_fresh ex_ids c rm2 /\ wf_freshs ex_ids cs' rm2 
end.

End SBpass.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)
