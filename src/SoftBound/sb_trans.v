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

Fixpoint trans_params (rm:rmap) (lp:params) : option params :=
match lp with
| nil => Some nil
| (t0,v0) as p::lp' =>
    match trans_params rm lp' with
    | None => None
    | Some lp2 =>
      if isPointerTypB t0 then
        match get_reg_metadata rm v0 with
        | Some (bv0, ev0) =>
            Some ((p8,bv0)::(p8,ev0)::lp2)
        | _ => None
        end
      else Some lp2
    end
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
       insn_gep tmp false (typ_pointer t1) (value_id id0) 
         (Cons_list_value v1 Nil_list_value) :: 
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
                  ((p8,v2)::
                   (p8,(value_id addrb))::
                   (p8,(value_id addre))::nil)::
                 insn_load bid0 p8 (value_id addrb) Align.Zero::
                 insn_load eid0 p8 (value_id addre) Align.Zero::   
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
          match get_reg_metadata rm v1 with
          | Some (bv0, ev0) =>
              Some
                (insn_call fake_id true false typ_void set_mmetadata_fn 
                  ((p8,(value_id ptmp))::
                   (p8,bv0)::
                   (p8,ev0)::nil)::
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

| insn_call id0 noret0 tailc0 rt fv lp =>
    do lp' <- trans_params rm lp;
    ret (ex_ids, tmps, [insn_call id0 noret0 tailc0 rt fv (lp++lp')])
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
            Some ((p8,bid0)::(p8,eid0)::la2)
        | _ => None
        end
      else Some la2
    end
end.

Definition insert_more_allocas (addrb addre:id) (b:block) : block :=
let '(block_intro l1 ps1 cs1 tmn1) := b in
block_intro l1 ps1
  (insn_alloca addrb p8 
    (value_const (const_int Size.ThirtyTwo (INTEGER.of_Z 32%Z 1%Z false))) 
    Align.Zero::
  insn_alloca addre p8 
    (value_const (const_int Size.ThirtyTwo (INTEGER.of_Z 32%Z 1%Z false))) 
    Align.Zero::cs1) tmn1.

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
        | Some (ex_ids, tmps, b'::bs') => 
            Some (rm, tmps, 
              fdef_intro 
                (fheader_intro t fid (la++la')) 
                ((insert_more_allocas addrb addre b')::bs'))
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
(forall lc gl b i bgv egv als lc' Mem1' tr addrb addre bid0 eid0 als' v, 
  MM1 b i = Some (SoftBound.mkMD bgv egv) ->
  getOperandValue TD Mem1 v lc gl = Some (ptr2GV TD (Vptr b i)) ->
  SimpleSE.dbCmds TD gl lc als Mem1
    (insn_call fake_id true false typ_void get_mmetadata_fn 
       ((p8,v)::
        (p8,(value_id addrb))::
        (p8,(value_id addre))::nil)::
     insn_load bid0 p8 (value_id addrb) Align.Zero::
     insn_load eid0 p8 (value_id addre) Align.Zero::   
     nil) lc' als' Mem1' tr ->
  lookupAL _ lc' bid0 = Some bgv /\
  lookupAL _ lc' bid0 = Some egv
) /\
(forall lc gl b i bgv egv als lc' Mem1' tr addrb addre bid0 eid0 als' v, 
  getOperandValue TD Mem1 v lc gl = Some (ptr2GV TD (Vptr b i)) ->
  SimpleSE.dbCmds TD gl lc als Mem1
    (insn_call fake_id true false typ_void get_mmetadata_fn 
       ((p8,v)::
        (p8,(value_id addrb))::
        (p8,(value_id addre))::nil)::
     insn_load bid0 p8 (value_id addrb) Align.Zero::
     insn_load eid0 p8 (value_id addre) Align.Zero::   
     nil) lc' als' Mem1' tr ->
  lookupAL _ lc' bid0 = Some bgv ->
  lookupAL _ lc' bid0 = Some egv ->
  MM1 b i = Some (SoftBound.mkMD bgv egv)
).

Fixpoint codom (rm:rmap) : atoms :=
match rm with
| nil => empty
| (_,(bid,eid))::rm' => singleton bid `union` singleton eid `union` codom rm'
end.

Lemma reg_simulation__updateAddAL : forall rm1 rm2 lc1 lc2 i0 gv',
  reg_simulation rm1 rm2 lc1 lc2 ->
  i0 `notin` codom rm2 ->
  reg_simulation rm1 rm2 (updateAddAL GenericValue lc1 i0 gv')
    (updateAddAL GenericValue lc2 i0 gv').
Admitted.

Lemma simulation__BOP : forall rm rm2 lc lc2 TD MM Mem Mem2 gl bop0 sz0 v1 v2 
                        gv3,
  reg_simulation rm rm2 lc lc2 ->
  mem_simulation TD MM Mem Mem2 ->
  BOP TD Mem lc gl bop0 sz0 v1 v2 = ret gv3 ->
  BOP TD Mem2 lc2 gl bop0 sz0 v1 v2 = ret gv3.
Admitted.

Lemma mem_simulation__malloc : forall TD MM Mem Mem2 tsz gn align0 Mem' mb,
  mem_simulation TD MM Mem Mem2 ->
  malloc TD Mem tsz gn align0 = ret (Mem', mb) ->
  exists Mem2',
    malloc TD Mem2 tsz gn align0 = ret (Mem2', mb) /\
    mem_simulation TD MM Mem' Mem2'.
Admitted.

Lemma simulation__getOperandValue : forall rm rm2 lc lc2 TD MM Mem Mem2 gl v gv,
  reg_simulation rm rm2 lc lc2 ->
  mem_simulation TD MM Mem Mem2 ->
  getOperandValue TD Mem v lc gl = ret gv ->
  getOperandValue TD Mem2 v lc2 gl = ret gv.
Admitted.

Lemma mem_simulation__free : forall TD MM Mem Mem2 mptr0 Mem',
  mem_simulation TD MM Mem Mem2 ->
  free TD Mem mptr0 = ret Mem' ->
  exists Mem2',
    free TD Mem2 mptr0 = ret Mem2' /\
    mem_simulation TD MM Mem' Mem2'.
Admitted.

Lemma trans_cmd__is__correct : forall c TD lc1 rm1 als gl Mem1 MM1 lc1' als' 
    Mem1' MM1' tr lc2 Mem2 rm2 rm1' cs ex_ids tmps addrb addre ex_ids' tmps' r,  
  getCmdID c `notin` codom rm2 ->
  trans_cmd ex_ids tmps addrb addre rm2 c = Some (ex_ids', tmps', cs) ->
  reg_simulation rm1 rm2 lc1 lc2 ->
  mem_simulation TD MM1 Mem1 Mem2 ->
  SoftBound.dbCmd TD gl lc1 rm1 als Mem1 MM1 c lc1' rm1' als' Mem1' MM1' tr r ->
  exists lc2', exists Mem2',
   SimpleSE.dbCmds TD gl lc2 als Mem2 cs lc2' als' Mem2' tr /\
   reg_simulation rm1' rm2 lc1' lc2' /\
   mem_simulation TD MM1' Mem1' Mem2'.
Proof.
  intros c TD lc1 rm1 als gl Mem1 MM1 lc1' als' Mem1' MM1' tr lc2 Mem2 rm2 rm1' 
    cs ex_ids tmps addrb addre ex_ids' tmps' r Hnotin Htrans Hrsim Hmsim HdbCmd.
  (sb_dbCmd_cases (destruct HdbCmd) Case); simpl in Htrans.

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

admit. admit. admit. admit. admit. admit. admit.

Case "dbMalloc".
  remember (lookupAL (id * id) rm2 id0) as R1.
  destruct R1; try solve [inversion Htrans].
  destruct p as [bid eid].
  remember (mk_tmp ex_ids) as R2.
  destruct R2 as [tmp ex_ids''].
  inv Htrans.
  invert_prop_reg_metadata.
  apply mem_simulation__malloc with (MM:=MM)(Mem2:=Mem2) in H1; auto.
  destruct H1 as [Mem2' [H11 H12]].
  exists 
    (updateAddAL _ 
      (updateAddAL _ 
        (updateAddAL _ 
          (updateAddAL GenericValue lc2 id0 (blk2GV TD mb))
          bid (SoftBound.base2GV TD mb))
        tmp (SoftBound.bound2GV TD mb tsz n))
      eid (SoftBound.bound2GV TD mb tsz n)).
  exists Mem2'.
  split.
    assert (trace_nil = trace_app trace_nil trace_nil) as EQ. auto.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL GenericValue lc2 id0 (blk2GV TD mb))(als2:=als)
      (Mem2:=Mem2'); auto.
      apply SimpleSE.dbMalloc with (gn:=gn)(tsz:=tsz); 
        eauto using simulation__getOperandValue.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _
              (updateAddAL GenericValue lc2 id0 (blk2GV TD mb))
              bid (SoftBound.base2GV TD mb)
      )
      (als2:=als)
      (Mem2:=Mem2'); auto.
      apply SimpleSE.dbCast; auto.
        admit.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _
              (updateAddAL _
                (updateAddAL GenericValue lc2 id0 (blk2GV TD mb))
                 bid (SoftBound.base2GV TD mb))
               tmp (SoftBound.bound2GV TD mb tsz n)
      )
      (als2:=als)
      (Mem2:=Mem2'); auto.
      apply SimpleSE.dbGEP with (mp:=blk2GV TD mb)(vidxs:=[gn]); auto.
        admit. admit. admit.
    rewrite EQ.
    apply SimpleSE.dbCmds_cons with 
      (lc2:=updateAddAL _
              (updateAddAL _
                (updateAddAL _
                  (updateAddAL GenericValue lc2 id0 (blk2GV TD mb))
                   bid (SoftBound.base2GV TD mb))
                 tmp (SoftBound.bound2GV TD mb tsz n))
               eid (SoftBound.bound2GV TD mb tsz n)
      )
      (als2:=als)
      (Mem2:=Mem2'); auto.
      apply SimpleSE.dbCast; auto.
        admit.

  split; auto.
    admit.

admit.    

Case "dbFree".
  inv Htrans.
  apply mem_simulation__free with (MM:=MM)(Mem2:=Mem2) in H0; auto.
  destruct H0 as [Mem2' [H01 H02]].
  exists lc2. exists Mem2'. 
  split.
   assert (trace_nil = trace_app trace_nil trace_nil) as EQ. auto.
   rewrite EQ.
   eapply SimpleSE.dbCmds_cons; eauto.
     apply SimpleSE.dbFree with (mptr:=mptr0); 
       eauto using simulation__getOperandValue.
  split; auto.

admit. admit. admit.

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
  destruct p as [bv ev].
  remember (mk_tmp ex_ids) as R1. 
  destruct R1 as [ptmp ex_ids1].
  remember (mk_tmp ex_ids1) as R2. 
  destruct R2 as [btmp ex_ids2].
  remember (mk_tmp ex_ids2) as R3. 
  destruct R3 as [etmp ex_ids3].
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
  destruct p as [bv ev].
  remember (mk_tmp ex_ids) as R1. 
  destruct R1 as [ptmp ex_ids1].
  remember (mk_tmp ex_ids1) as R2. 
  destruct R2 as [btmp ex_ids2].
  remember (mk_tmp ex_ids2) as R3. 
  destruct R3 as [etmp ex_ids3].
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
  destruct p as [bv ev].
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
  destruct p as [bv ev].
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

    unfold isPointerTyp in H4.
    rewrite <- HeqR4 in H4.
    inversion H4.

admit. admit. admit.

Case "dbStore_abort".
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
    Mem1' MM1' tr lc2 Mem2 rm2 rm1' cs' ex_ids tmps addrb addre ex_ids' tmps' r, 
  AtomSetImpl.inter (getCmdsIDs cs) (codom rm2) [<=] empty ->
  trans_cmds ex_ids tmps addrb addre rm2 cs = Some (ex_ids', tmps', cs') ->
  reg_simulation rm1 rm2 lc1 lc2 ->
  mem_simulation TD MM1 Mem1 Mem2 ->
  SoftBound.dbCmds TD gl lc1 rm1 als Mem1 MM1 cs lc1' rm1' als' Mem1' MM1' tr r 
    ->
  exists lc2', exists Mem2',
    SimpleSE.dbCmds TD gl lc2 als Mem2 cs' lc2' als' Mem2' tr /\
    reg_simulation rm1' rm2 lc1' lc2' /\
    mem_simulation TD MM1' Mem1' Mem2'.
Admitted.

(* Validation *)

(*
Require Import sub_tv_def.

Fixpoint tv_sterm fid (st st':sterm) : bool :=
match (st, st') with
| (sterm_val v, sterm_val v') => tv_value fid v v'
| (sterm_bop b sz st1 st2, sterm_bop b' sz' st1' st2') =>
    sumbool2bool _ _ (bop_dec b b') && sumbool2bool _ _ (Size.dec sz sz') &&
    tv_sterm fid st1 st1' && tv_sterm fid st2 st2'
| (sterm_fbop b f st1 st2, sterm_fbop b' f' st1' st2') =>
    sumbool2bool _ _ (fbop_dec b b') && 
    sumbool2bool _ _ (floating_point_dec f f') &&
    tv_sterm fid st1 st1' && tv_sterm fid st2 st2'
| (sterm_extractvalue t st1 cs, sterm_extractvalue t' st1' cs') =>
    tv_typ t t' && tv_sterm fid st1 st1' &&
  sumbool2bool _ _ (list_const_dec cs cs')
| (sterm_insertvalue t1 st1 t2 st2 cs, 
   sterm_insertvalue t1' st1' t2' st2' cs') =>
    tv_typ t1 t1' && tv_sterm fid st1 st1' && 
    tv_typ t2 t2' && tv_sterm fid st2 st2' &&
    sumbool2bool _ _ (list_const_dec cs cs')
| (sterm_malloc sm t st1 a, sterm_malloc sm' t' st1' a') =>
    tv_smem fid sm sm' && tv_typ t t' && 
    tv_sterm fid st1 st1' && tv_align a a'
| (sterm_alloca sm t st1 a, sterm_alloca sm' t' st1' a') =>
    tv_smem fid sm sm' && tv_typ t t' && 
    tv_sterm fid st1 st1' && tv_align a a'
| (sterm_load sm t st1 a, sterm_load sm' t' st1' a') =>
    tv_smem fid sm sm' && tv_typ t t' && 
    tv_sterm fid st1 st1' && tv_align a a'
| (sterm_gep i t st1 sts2, sterm_gep i' t' st1' sts2') =>
    sumbool2bool _ _ (bool_dec i i') && tv_typ t t' &&
    tv_sterm fid st1 st1' && tv_list_sterm fid sts2 sts2'
| (sterm_trunc top t1 st1 t2, sterm_trunc top' t1' st1' t2') =>
    sumbool2bool _ _ (truncop_dec top top') && tv_typ t1 t1' &&
    tv_sterm fid st1 st1' && tv_typ t2 t2'
| (sterm_ext eo t1 st1 t2, sterm_ext eo' t1' st1' t2') =>
    sumbool2bool _ _ (extop_dec eo eo') && tv_typ t1 t1' &&
    tv_sterm fid st1 st1' && tv_typ t2 t2' 
| (sterm_cast co t1 st1 t2, sterm_cast co' t1' st1' t2') =>
    sumbool2bool _ _ (castop_dec co co') && tv_typ t1 t1' &&
    tv_sterm fid st1 st1' && tv_typ t2 t2' 
| (sterm_icmp c t st1 st2, sterm_icmp c' t' st1' st2') =>
    sumbool2bool _ _ (cond_dec c c') && tv_typ t t' &&
    tv_sterm fid st1 st1' && tv_sterm fid st2 st2'
| (sterm_fcmp c ft st1 st2, sterm_fcmp c' ft' st1' st2') =>
    sumbool2bool _ _ (fcond_dec c c') &&
    sumbool2bool _ _ (floating_point_dec ft ft') &&
    tv_sterm fid st1 st1' && tv_sterm fid st2 st2'
| (sterm_phi t stls, sterm_phi t' stls') =>
    tv_typ t t' && tv_list_sterm_l fid stls stls'
| (sterm_select st1 t st2 st3, sterm_select st1' t' st2' st3') =>
    tv_sterm fid st1 st1' && tv_typ t t' && 
    tv_sterm fid st2 st2' && tv_sterm fid st3 st3'
| (sterm_lib sm i sts, sterm_lib sm' i' sts') =>
    tv_smem fid sm sm' && eq_id i i' && 
    tv_list_sterm fid sts sts'
| _ => false
end
with tv_list_sterm fid (sts sts':list_sterm) : bool :=
match (sts, sts') with
| (Nil_list_sterm, Nil_list_sterm) => true
| (Cons_list_sterm st sts0, Cons_list_sterm st' sts0') =>
    tv_sterm fid st st' && tv_list_sterm fid sts0 sts0'
| _ => false
end
with tv_list_sterm_l fid (stls stls':list_sterm_l) : bool :=
match (stls, stls') with
| (Nil_list_sterm_l, Nil_list_sterm_l) => true
| (Cons_list_sterm_l st l stls0, Cons_list_sterm_l st' l' stls0') =>
    tv_sterm fid st st' && sumbool2bool _ _ (l_dec l l') && 
    tv_list_sterm_l fid stls0 stls0'
| _ => false
end
with tv_smem fid (sm1 sm2:smem) : bool :=
match (sm1, sm2) with
| (smem_init, _) => true
| (smem_malloc sm1 t1 st1 a1, smem_malloc sm2 t2 st2 a2) =>
    tv_smem fid sm1 sm2 && tv_typ t1 t2 && 
    tv_sterm fid st1 st2 && tv_align a1 a2
| (smem_alloca sm1 t1 st1 a1, smem_alloca sm2 t2 st2 a2) =>
    tv_smem fid sm1 sm2 && tv_typ t1 t2 && 
    tv_sterm fid st1 st2 && tv_align a1 a2
| (smem_free sm1 t1 st1, smem_free sm2 t2 st2) =>
    tv_smem fid sm1 sm2 && tv_typ t1 t2 && tv_sterm fid st1 st2
| (smem_load sm1 t1 st1 a1, smem_load sm2 t2 st2 a2) =>
    tv_smem fid sm1 sm2 && tv_typ t1 t2 && 
    tv_sterm fid st1 st2 && tv_align a1 a2
| (smem_store sm1 t1 st11 st12 a1, smem_store sm2 t2 st21 st22 a2) =>
    tv_smem fid sm1 sm2 && tv_typ t1 t2 && 
    tv_sterm fid st11 st21 &&
    tv_sterm fid st12 st22 && tv_align a1 a2
| (smem_lib sm1 fid1 sts1, smem_lib sm2 fid2 sts2) => 
    tv_smem fid sm1 sm2 && eq_id fid1 fid2 && 
    tv_list_sterm fid sts1 sts2
| _ => false
end.

Fixpoint tv_sframe fid (sf1 sf2:sframe) : bool :=
match (sf1, sf2) with
| (sframe_init, _) => true
| (sframe_alloca sm1 sf1 t1 st1 a1, sframe_alloca sm2 sf2 t2 st2 a2) =>
    tv_smem fid sm1 sm2 && tv_typ t1 t2 && 
    tv_sterm fid st1 st2 && tv_align a1 a2 &&
    tv_sframe fid sf1 sf2
| _ => false
end.

Fixpoint tv_smap fid (rm1:rmap) (rm2:metadata) (sm1 sm2:smap) : bool :=
match sm1 with
| nil => true
| (id1,st1)::sm1' =>
  match (lookupAL _ sm2 (rename_id fid id1), 
         lookupAL _ with
  | None => false
  | Some st2 => tv_sterm Ps1 Ps2 fid st1 st2 && tv_smap Ps1 Ps2 fid sm1' sm2
  end
end.
*)

End SBpass.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)
