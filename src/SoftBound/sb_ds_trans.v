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
Require Import alist.
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
Require Import sb_db_trans.

Import SBpass.

Module SB_ds_pass.

Parameter set_shadowstack_base_fid : id.
Parameter set_shadowstack_bound_fid : id.
Parameter get_shadowstack_base_fid : id.
Parameter get_shadowstack_bound_fid : id.
Parameter allocate_shadowstack_fid : id.
Parameter free_shadowstack_fid : id.

Definition set_shadowstack_base_typ : typ :=
  typ_function typ_void 
        (Cons_list_typ p8 
        (Cons_list_typ i32 Nil_list_typ)) false.

Definition set_shadowstack_base_fn : value :=
  value_const (const_gid set_shadowstack_base_typ set_shadowstack_base_fid).

Definition set_shadowstack_bound_typ : typ :=
  typ_function typ_void 
        (Cons_list_typ p8 
        (Cons_list_typ i32 Nil_list_typ)) false.

Definition set_shadowstack_bound_fn : value :=
  value_const (const_gid set_shadowstack_bound_typ set_shadowstack_bound_fid).

Definition get_shadowstack_base_typ : typ :=
  typ_function p8 (Cons_list_typ i32 Nil_list_typ) false.

Definition get_shadowstack_base_fn : value :=
  value_const (const_gid get_shadowstack_base_typ get_shadowstack_base_fid).

Definition get_shadowstack_bound_typ  : typ :=
 typ_function p8 (Cons_list_typ i32 Nil_list_typ) false.

Definition get_shadowstack_bound_fn : value :=
  value_const (const_gid get_shadowstack_bound_typ get_shadowstack_bound_fid).

Definition allocate_shadowstack_typ : typ :=
  typ_function typ_void (Cons_list_typ i32 Nil_list_typ) false.

Definition allocate_shadowstack_fn : value :=
  value_const (const_gid allocate_shadowstack_typ allocate_shadowstack_fid).

Definition free_shadowstack_typ : typ :=
  typ_function typ_void Nil_list_typ false.

Definition free_shadowstack_fn : value :=
  value_const (const_gid free_shadowstack_typ free_shadowstack_fid).

Fixpoint get_const_metadata (c:const) : option (const*const) :=
match c with
| const_gid t gid => 
    match t with
    | typ_function _ _ _ => Some (const_castop castop_bitcast c p8,
                                  const_castop castop_bitcast c p8)
    | _ => Some (const_castop castop_bitcast c p8,
                 const_castop castop_bitcast 
                   (const_gep false c 
                   (Cons_list_const (const_int Size.ThirtyTwo 
                   (INTEGER.of_Z 32%Z 1%Z false)) Nil_list_const)) p8)
    end
| const_gep _ pc _ => get_const_metadata pc
| _ => None
end.

Definition get_reg_metadata (rm:rmap) (v:value) : option (value * value) :=
  match v with
  | value_id pid => 
      match lookupAL _ rm pid with
      | Some (bid, eid) => Some (value_id bid, value_id eid)
      | None => None
      end
  | value_const c => 
      match (get_const_metadata c, Constant.getTyp c) with
      | (Some (bc, ec), _) => Some (value_const bc, value_const ec)
      | (None, Some t) => Some (value_const (const_null p8), 
                                value_const (const_null p8))
      | _ => None
      end
  end.

Fixpoint trans_params (rm:rmap) (lp:params) (idx:Z) (cs:cmds) : option (cmds*Z) 
  :=
match lp with
| nil => Some (cs, idx)
| (t0,v0) as p::lp' =>
    if isPointerTypB t0 then
      match get_reg_metadata rm v0 with
      | Some (bv0, ev0) =>
            trans_params rm lp' (idx+1)
               (insn_call fake_id true sb_call_attrs
                 set_shadowstack_base_typ set_shadowstack_base_fn
                 ((p8,bv0)::
                  (i32,(value_const (const_int Size.ThirtyTwo 
                         (INTEGER.of_Z 32%Z idx false))))::
                   nil)::               
               insn_call fake_id true sb_call_attrs
                 set_shadowstack_bound_typ set_shadowstack_bound_fn
                 ((p8,ev0)::
                  (i32,(value_const (const_int Size.ThirtyTwo 
                         (INTEGER.of_Z 32%Z idx false))))::
                   nil)::               
                   cs)
      | _ => None
      end
    else trans_params rm lp' idx cs
end.

Definition int0 := const_int Size.ThirtyTwo (INTEGER.of_Z 32%Z 0%Z false).
Definition vint0 := value_const int0.

Axiom wrapper_fid : id -> id.

Definition isPointerTypB' t0 : bool :=
match t0 with
| typ_function t0 _ _ => isPointerTypB t0
| _ => false
end.

Definition trans_cmd (ex_ids tmps:ids) (optaddrb optaddre:option id)
  (rm:rmap) (c:cmd) : option (ids*ids*cmds*option id*option id) :=
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
    | Some (bv, ev) =>
      let '(ptmp,ex_ids) := mk_tmp ex_ids in
      let '(optcs, ex_ids, tmps, optaddrb, optaddre) := 
        if isPointerTypB t2 then
          match lookupAL _ rm id0 with
          | Some (bid0, eid0) =>
              match (optaddrb, optaddre) with
              | (Some addrb, Some addre) =>
                   (Some
                     (insn_call fake_id true sb_call_attrs
                       get_mmetadata_typ get_mmetadata_fn 
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
                     (insn_call fake_id true sb_call_attrs
                       get_mmetadata_typ get_mmetadata_fn 
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
        Some (ex_ids, ptmp::tmps,
         insn_cast ptmp castop_bitcast (typ_pointer t2) v2 p8:: 
         insn_call fake_id true sb_call_attrs assert_mptr_typ assert_mptr_fn 
           ((p8,bv)::
            (p8,ev)::
            (p8,(value_id ptmp))::
            (i32,type_size t2)::
            (i32,vint1)::nil)::
         c::
         cs, optaddrb, optaddre)
      end
    | None => None
    end

| insn_store id0 t0 v1 v2 align =>
    match get_reg_metadata rm v2 with
    | Some (bv, ev) =>
      let '(ptmp,ex_ids) := mk_tmp ex_ids in
      let optcs := 
        if isPointerTypB t0 then
          match get_reg_metadata rm v1 with
          | Some (bv0, ev0) =>
              Some
                (insn_call fake_id true sb_call_attrs set_mmetadata_typ 
                  set_mmetadata_fn 
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
        Some (ex_ids, ptmp::tmps,
         insn_cast ptmp castop_bitcast (typ_pointer t0) v2 p8:: 
         insn_call fake_id true sb_call_attrs assert_mptr_typ assert_mptr_fn 
           ((p8,bv)::
            (p8,ev)::
            (p8,(value_id ptmp))::
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
      | (Some (bv1, ev1), Some (bv2, ev2), Some (bid0, eid0)) =>
          Some (ex_ids, tmps,
            c::
            insn_select bid0 v0 p8 bv1 bv2:: 
            insn_select eid0 v0 p8 ev1 ev2:: 
            nil, optaddrb, optaddre)
      | _ => None
      end
    else Some (ex_ids, tmps, [c], optaddrb, optaddre)

| insn_call i0 n t t0 v p =>
    match
      (match v with
       | value_const (const_gid ft fid) =>
           if isSysLib fid then
              (Some (nil, 0%Z), v)
           else (trans_params rm p 1%Z nil, 
                 value_const (const_gid ft (wrapper_fid fid)))
       | _ => (trans_params rm p 1%Z nil, v)
      end) with
    | (Some (cs, num), v') =>
        let optcs' :=
          if isPointerTypB' t0 then
            match (lookupAL _ rm i0) with
            | Some (bid0, eid0) =>
                Some (
                  insn_call bid0 false sb_call_attrs 
                    get_shadowstack_base_typ get_shadowstack_base_fn  
                    ((i32,vint0)::nil)::
                  insn_call eid0 false sb_call_attrs
                    get_shadowstack_bound_typ get_shadowstack_bound_fn 
                    ((i32,vint0)::nil)::
                  insn_call fake_id true sb_call_attrs
                    free_shadowstack_typ free_shadowstack_fn nil::
                  nil)
            | None => None
            end
          else 
            Some [insn_call fake_id true sb_call_attrs
                    free_shadowstack_typ free_shadowstack_fn nil]
        in
        match optcs' with
        | Some cs' =>
            Some (ex_ids, tmps, 
                  insn_call fake_id true sb_call_attrs
                    allocate_shadowstack_typ allocate_shadowstack_fn
                    ((i32,(value_const (const_int Size.ThirtyTwo 
                       (INTEGER.of_Z 32%Z num false))))::
                     nil)::               
                  cs++[insn_call i0 n t t0 v' p]++cs',
                  optaddrb, optaddre)
        | None => None
        end
    | (None, _) => None
    end

| _ => Some (ex_ids, tmps, [c], optaddrb, optaddre)
end.

Fixpoint trans_cmds (ex_ids tmps:ids) (optaddrb optaddre:option id) 
  (rm:rmap) (cs:list cmd) : option (ids*ids*cmds*option id*option id) :=
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

Definition trans_block (ex_ids tmps:ids) (optaddrb optaddre:option id) (rm:rmap)
  (b:block) : option (ids*ids*option id*option id*block) :=
let '(block_intro l1 ps1 cs1 tmn1) := b in
match trans_phinodes rm ps1 with
| None => None
| Some ps2 => 
    match trans_cmds ex_ids tmps optaddrb optaddre rm cs1 with
    | Some (ex_ids',tmps',cs2,optaddrb,optaddre) => 
        let opt :=
          match tmn1 with
          | insn_return _ t0 v0 =>
            if isPointerTypB t0 then
              match get_reg_metadata rm v0 with
              | Some (bv, ev) =>
                  Some (
                   insn_call fake_id true sb_call_attrs
                     set_shadowstack_base_typ set_shadowstack_base_fn
                     ((p8,bv)::(i32,vint0)::nil)::
                   insn_call fake_id true sb_call_attrs
                     set_shadowstack_bound_typ set_shadowstack_bound_fn
                     ((p8,ev)::(i32,vint0)::nil)::
                   nil)
              | None => None
              end
            else 
              Some nil
          | _ => Some nil
          end
        in
        match opt with
        | Some cs' =>
            Some (ex_ids',tmps',optaddrb,optaddre, 
              block_intro l1 ps2 (cs2++cs') tmn1)
        | _ => None
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

Fixpoint trans_args (rm:rmap) (la:args) (idx:Z) (cs:cmds) : option cmds :=
match la with
| nil => Some cs
| (t0,_,id0)::la' =>
    if isPointerTypB t0 then
      match (lookupAL _ rm id0) with
      | Some (bid0, eid0) => 
          trans_args rm la' (idx+1)
                (insn_call bid0 false sb_call_attrs
                   get_shadowstack_base_typ get_shadowstack_base_fn  
                   ((i32,(value_const (const_int Size.ThirtyTwo 
                         (INTEGER.of_Z 32%Z idx false))))::nil)::
                 insn_call eid0 false sb_call_attrs
                   get_shadowstack_bound_typ get_shadowstack_bound_fn 
                   ((i32,(value_const (const_int Size.ThirtyTwo 
                         (INTEGER.of_Z 32%Z idx false))))::nil)::
                 cs)
      | _ => None
      end
    else trans_args rm la' idx cs
end.

Definition insert_more_allocas (optaddrb optaddre:option id) (argsmd:cmds) 
  (b:block) : block :=
let '(block_intro l1 ps1 cs1 tmn1) := b in  
match (optaddrb, optaddre) with
| (Some addrb, Some addre) =>
  block_intro l1 ps1
    (insn_alloca addrb p8 vint1 Align.Zero::
    insn_alloca addre p8 vint1 Align.Zero::argsmd++cs1) tmn1
| _ => 
    block_intro l1 ps1 (argsmd++cs1) tmn1
end.

Definition trans_fdef nts (f:fdef) : option fdef :=
let '(fdef_intro (fheader_intro fa t fid la va) bs) := f in
if SimpleSE.isCallLib fid then Some f
else
  let ex_ids := getFdefLocs f in
  match gen_metadata_fdef nts ex_ids nil f with
  | Some (ex_ids,rm) =>
      match (trans_args rm la 1%Z nil) with
      | Some cs' =>
          match (trans_blocks ex_ids nil None None rm bs) with
          | Some (ex_ids, tmps, optaddrb, optaddre, b'::bs') => 
              Some (fdef_intro 
                     (fheader_intro fa t (wrapper_fid fid) la va) 
                     ((insert_more_allocas optaddrb optaddre cs' b')::bs'))
          | _ => None
          end
      | _ => None
      end
  | None => None
  end.

Definition trans_fdec (f:fdec) : fdec :=
let '(fdec_intro (fheader_intro fa t fid la va)) := f in
fdec_intro (fheader_intro fa t (wrapper_fid fid) la va). 

Fixpoint trans_product nts (p:product) : option product :=
match p with
| product_fdef f =>
    match trans_fdef nts f with
    | None => None
    | Some f' => Some (product_fdef f')
    end
| product_fdec f => Some (product_fdec (trans_fdec f))
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

End SB_ds_pass.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)
