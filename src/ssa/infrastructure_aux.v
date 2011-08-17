(* These libs are only used when typechecking ssa_coq_lib.v alone.
   They are not copied into the final ssa.v, otherwise the definitions in ssa_def,
   and ssa are conflict, since they define same syntax. For example, we may have
   ssa_def.insn and insn in ssa, but they are same. This is fixed if we dont copy
   the libs below into ssa_coq.ott.
*)
Add LoadPath "./ott".
Add LoadPath "./monads".
Add LoadPath "./compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import syntax.
Require Import Metatheory.

(*BEGINCOPY*)

Require Import List.
Require Import ListSet.
Require Import Bool.
Require Import Arith.
Require Import Compare_dec.
Require Import Recdef.
Require Import Coq.Program.Wf.
Require Import Omega.
Require Import monad.
Require Import Decidable.
Require Import alist.
Require Import Integers.
Require Import Coqlib.
Require Import Maps.
Require Import Memory.
Require Import Kildall.
Require Import Lattice.
Require Import targetdata.

Module LLVMinfra.

Export LLVMsyntax.

(**********************************)
(* Definition for basic types, which can be refined for extraction. *)

Definition id_dec : forall x y : id, {x=y} + {x<>y} := eq_atom_dec.
Definition l_dec : forall x y : l, {x=y} + {x<>y} := eq_atom_dec.
Definition inbounds_dec : forall x y : inbounds, {x=y} + {x<>y} := bool_dec.
Definition tailc_dec : forall x y : tailc, {x=y} + {x<>y} := bool_dec.
Definition varg_dec : forall x y : varg, {x=y} + {x<>y} := bool_dec.
Definition noret_dec : forall x y : noret, {x=y} + {x<>y} := bool_dec.

(**********************************)
(* LabelSet. *)

  Definition lempty_set := empty_set l.
  Definition lset_add (l1:l) (ls2:ls) := set_add eq_dec l1 ls2.
  Definition lset_union (ls1 ls2:ls) := set_union eq_dec ls1 ls2.
  Definition lset_inter (ls1 ls2:ls) := set_inter eq_dec ls1 ls2.
  Definition lset_eqb (ls1 ls2:ls) := 
    match (lset_inter ls1 ls2) with
    | nil => true
    | _ => false
    end.
  Definition lset_neqb (ls1 ls2:ls) := 
    match (lset_inter ls1 ls2) with
    | nil => false
    | _ => true
    end.
  Definition lset_eq (ls1 ls2:ls) := lset_eqb ls1 ls2 = true.
  Definition lset_neq (ls1 ls2:ls) := lset_neqb ls1 ls2 = true. 
  Definition lset_single (l0:l) := lset_add l0 (lempty_set). 
  Definition lset_mem (l0:l) (ls0:ls) := set_mem eq_dec l0 ls0.

(**********************************)
(* Inversion. *)

  Definition getCmdLoc (i:cmd) : id :=
  match i with
  | insn_bop id _ sz v1 v2 => id
  | insn_fbop id _ _ _ _ => id
  (* | insn_extractelement id typ0 id0 c1 => id *)
  (* | insn_insertelement id typ0 id0 typ1 v1 c2 => id *)
  | insn_extractvalue id typs id0 c1 => id
  | insn_insertvalue id typs id0 typ1 v1 c2 => id 
  | insn_malloc id _ _ _ => id
  | insn_free id _ _ => id
  | insn_alloca id _ _ _ => id
  | insn_load id typ1 v1 _ => id
  | insn_store id typ1 v1 v2 _ => id
  | insn_gep id _ _ _ _ => id
  | insn_trunc id _ typ1 v1 typ2 => id 
  | insn_ext id _ sz1 v1 sz2 => id
  | insn_cast id _ typ1 v1 typ2 => id
  | insn_icmp id cond typ v1 v2 => id
  | insn_fcmp id cond typ v1 v2 => id 
  | insn_select id v0 typ v1 v2 => id
  | insn_call id _ _ typ v0 paraml => id
  end.
 
  Definition getTerminatorID (i:terminator) : id :=
  match i with
  | insn_return id t v => id
  | insn_return_void id => id
  | insn_br id v l1 l2 => id
  | insn_br_uncond id l => id
  (* | insn_switch id t v l _ => id *)
  (* | insn_invoke id typ id0 paraml l1 l2 => id *)
  | insn_unreachable id => id
  end.

  Definition getPhiNodeID (i:phinode) : id :=
  match i with
  | insn_phi id _ _ => id
  end.

  Definition getValueID (v:value) : option id :=
  match v with
  | value_id id => Some id
  | value_const _ => None
  end.

  Definition getInsnLoc (i:insn) : id :=
  match i with
  | insn_phinode p => getPhiNodeID p
  | insn_cmd c => getCmdLoc c
  | insn_terminator t => getTerminatorID t
  end.

  Definition isPhiNodeB (i:insn) : bool :=
  match i with
  | insn_phinode p => true
  | insn_cmd c => false
  | insn_terminator t => false
  end.  

  Definition isPhiNode (i:insn) : Prop :=
  isPhiNodeB i = true.

  Definition getCmdID (i:cmd) : option id :=
  match i with
  | insn_bop id _ sz v1 v2 => Some id
  | insn_fbop id _ _ _ _ => Some id 
  (* | insn_extractelement id typ0 id0 c1 => id *)
  (* | insn_insertelement id typ0 id0 typ1 v1 c2 => id *)
  | insn_extractvalue id typs id0 c1 => Some id
  | insn_insertvalue id typs id0 typ1 v1 c2 => Some id 
  | insn_malloc id _ _ _ => Some id
  | insn_free id _ _ => None
  | insn_alloca id _ _ _ => Some id
  | insn_load id typ1 v1 _ => Some id
  | insn_store id typ1 v1 v2 _ => None
  | insn_gep id _ _ _ _ => Some id
  | insn_trunc id _ typ1 v1 typ2 => Some id 
  | insn_ext id _ sz1 v1 sz2 => Some id
  | insn_cast id _ typ1 v1 typ2 => Some id
  | insn_icmp id cond typ v1 v2 => Some id
  | insn_fcmp id cond typ v1 v2 => Some id 
  | insn_select id v0 typ v1 v2 => Some id
  | insn_call id nr _ typ v0 paraml => if nr then None else Some id
  end.

Fixpoint getCmdsIDs (cs:cmds) : list atom :=
match cs with
| nil => nil
| c::cs' =>
    match getCmdID c with 
    | Some id1 => id1::getCmdsIDs cs'
    | None => getCmdsIDs cs'
    end
end.

Fixpoint getPhiNodesIDs (ps:phinodes) : list atom :=
match ps with
| nil => nil
| p::ps' =>getPhiNodeID p::getPhiNodesIDs ps'
end.

Definition getBlockIDs (b:block) : list atom :=
let '(block_intro _ ps cs _) := b in
getPhiNodesIDs ps ++ getCmdsIDs cs.

Fixpoint getArgsIDs (la:args) : list atom :=
match la with
| nil => nil
| (_,id1)::la' => id1::getArgsIDs la'
end.

  Definition getInsnID (i:insn) : option id :=
  match i with
  | insn_phinode p => Some (getPhiNodeID p)
  | insn_cmd c => getCmdID c
  | insn_terminator t => None
  end.

Lemma getCmdLoc_getCmdID : forall a i0,
  getCmdID a = Some i0 ->
  getCmdLoc a = i0.
Proof.
  intros a i0 H.
  destruct a; inv H; auto.
    simpl. destruct n; inv H1; auto.
Qed.

Fixpoint mgetoffset_aux (TD:LLVMtd.TargetData) (t:typ) (idxs:list Z) (accum:Z) 
  : option (Z * typ) := 
  match idxs with
  | nil => Some (accum, t)
  | idx::idxs' =>
     match t with
     | typ_array _ t' =>
         match (LLVMtd.getTypeAllocSize TD t') with
         | Some sz => 
             mgetoffset_aux TD t' idxs' (accum + (Z_of_nat sz) * idx)
         | _ => None
         end
     | typ_struct lt => 
         match (LLVMtd.getStructElementOffset TD t (Coqlib.nat_of_Z idx)) 
         with
         | Some ofs =>
             do t' <- nth_list_typ (Coqlib.nat_of_Z idx) lt;
               mgetoffset_aux TD t' idxs' (accum + (Z_of_nat ofs))
         | _ => None
         end
     | _ => None
     end
  end.  

Definition mgetoffset (TD:LLVMtd.TargetData) (t:typ) (idxs:list Z) 
  : option (Z * typ) := 
(*let (_, nts) := TD in
do ut <- Constant.typ2utyp nts t;*)
mgetoffset_aux TD t idxs 0.

Fixpoint intConsts2Nats (TD:LLVMtd.TargetData) (lv:list_const) 
  : option (list Z):=
match lv with
| Nil_list_const => Some nil
| Cons_list_const (const_int sz0 n) lv' => 
  if Size.dec sz0 Size.ThirtyTwo 
  then
    match (intConsts2Nats TD lv') with
    | Some ns => Some ((INTEGER.to_Z n)::ns)
    | None => None
    end
  else None
| _ => None
end.

(** Statically idx for struct must be int, and idx for arr can be
    anything without checking bounds. *)
Fixpoint getSubTypFromConstIdxs (idxs : list_const) (t : typ) : option typ :=
match idxs with
| Nil_list_const => Some t 
| Cons_list_const idx idxs' => 
  match t with
  | typ_array sz t' => getSubTypFromConstIdxs idxs' t'
  | typ_struct lt => 
    match idx with
    | (const_int sz i) =>
      match (nth_list_typ (INTEGER.to_nat i) lt) with
      | Some t' => getSubTypFromConstIdxs idxs' t'
      | None => None
      end
    | _ => None
    end
  | _ => None
  end
end.

Definition getConstGEPTyp (idxs : list_const) (t : typ) : option typ :=
match (idxs, t) with
| (Cons_list_const idx idxs', typ_pointer t0)  =>
     (* The input t is already an element of a pointer typ *)
     match (getSubTypFromConstIdxs idxs' t0) with
     | Some t' => Some (typ_pointer t')
     | _ => None
     end
| _ => None
end.

Fixpoint getSubTypFromValueIdxs (idxs : list_value) (t : typ) : option typ :=
match idxs with
| Nil_list_value => Some t 
| Cons_list_value idx idxs' => 
  match t with
  | typ_array sz t' => getSubTypFromValueIdxs idxs' t'
  | typ_struct lt => 
    match idx with
    | value_const (const_int sz i) =>
      match (nth_list_typ (INTEGER.to_nat i) lt) with
      | Some t' => getSubTypFromValueIdxs idxs' t'
      | None => None
      end
    | _ => None
    end
  | _ => None
  end
end.

Definition getGEPTyp (idxs : list_value) (t : typ) : option typ :=
match idxs with
| Nil_list_value => None
| Cons_list_value idx idxs' =>
     (* The input t is already an element of a pointer typ *)
     match (getSubTypFromValueIdxs idxs' t) with
     | Some t' => Some (typ_pointer t')
     | _ => None
     end
end.

Definition getCmdTyp (i:cmd) : option typ :=
match i with
| insn_bop _ _ sz _ _ => Some (typ_int sz)
| insn_fbop _ _ ft _ _ => Some (typ_floatpoint ft)
(*
| insn_extractelement _ typ _ _ => getElementTyp typ
| insn_insertelement _ typ _ _ _ _ => typ *)
| insn_extractvalue _ typ _ idxs => getSubTypFromConstIdxs idxs typ
| insn_insertvalue _ typ _ _ _ _ => Some typ
| insn_malloc _ typ _ _ => Some (typ_pointer typ)
| insn_free _ typ _ => Some typ_void
| insn_alloca _ typ _ _ => Some (typ_pointer typ)
| insn_load _ typ _ _ => Some typ
| insn_store _ _ _ _ _ => Some typ_void
| insn_gep _ _ typ _ idxs => getGEPTyp idxs typ
| insn_trunc _ _ _ _ typ => Some typ
| insn_ext _ _ _ _ typ2 => Some typ2
| insn_cast _ _ _ _ typ => Some typ
| insn_icmp _ _ _ _ _ => Some (typ_int Size.One)
| insn_fcmp _ _ _ _ _ => Some (typ_int Size.One)
| insn_select _ _ typ _ _ => Some typ
| insn_call _ true _ typ _ _ => Some typ_void
| insn_call _ false _ typ _ _ =>
    match typ with
    | typ_function t _ _ => Some t
    | _ => None
    end
end.

Definition getTerminatorTyp (i:terminator) : typ :=
match i with
| insn_return _ typ _ => typ
| insn_return_void _ => typ_void
| insn_br _ _ _ _ => typ_void
| insn_br_uncond _ _ => typ_void
(* | insn_switch _ typ _ _ _ => typ_void *)
(* | insn_invoke _ typ _ _ _ _ => typ *)
| insn_unreachable _ => typ_void
end.

Definition getPhiNodeTyp (i:phinode) : typ :=
match i with
| insn_phi _ typ _ => typ
end.

Definition getInsnTyp (i:insn) : option typ :=
match i with
| insn_phinode p => Some (getPhiNodeTyp p)
| insn_cmd c => getCmdTyp c
| insn_terminator t => Some (getTerminatorTyp t)
end.

Definition getPointerEltTyp (t:typ) : option typ :=
match t with
| typ_pointer t' => Some t' 
| _ => None
end.

Definition getValueIDs (v:value) : ids :=
match (getValueID v) with
| None => nil
| Some id => id::nil
end.

Fixpoint values2ids (vs:list value) : ids :=
match vs with
| nil => nil
| value_id id::vs' => id::values2ids vs'
| _::vs' => values2ids vs'
end.

Definition getParamsOperand (lp:params) : ids :=
let '(_,vs) := split lp in values2ids vs.

Fixpoint list_prj1 (X Y:Type) (ls : list (X*Y)) : list X :=
match ls with
| nil => nil
| (x, y)::ls' => x::list_prj1 X Y ls'
end.

Fixpoint list_prj2 (X Y:Type) (ls : list (X*Y)) : list Y :=
match ls with
| nil => nil
| (x, y)::ls' => y::list_prj2 X Y ls'
end.

Definition getCmdOperands (i:cmd) : ids :=
match i with
| insn_bop _ _ _ v1 v2 => getValueIDs v1 ++ getValueIDs v2
| insn_fbop _ _ _ v1 v2 => getValueIDs v1 ++ getValueIDs v2
(* | insn_extractelement _ _ v _ => getValueIDs v
| insn_insertelement _ _ v1 _ v2 _ => getValueIDs v1 ++ getValueIDs v2
*)
| insn_extractvalue _ _ v _ => getValueIDs v
| insn_insertvalue _ _ v1 _ v2 _ => getValueIDs v1 ++ getValueIDs v2
| insn_malloc _ _ v _ => getValueIDs v
| insn_free _ _ v => getValueIDs v
| insn_alloca _ _ v _ => getValueIDs v
| insn_load _ _ v _ => getValueIDs v
| insn_store _ _ v1 v2 _ => getValueIDs v1 ++ getValueIDs v2
| insn_gep _ _ _ v vs => getValueIDs v ++ values2ids (unmake_list_value vs)
| insn_trunc _ _ _ v _ => getValueIDs v
| insn_ext _ _ _ v1 typ2 => getValueIDs v1
| insn_cast _ _ _ v _ => getValueIDs v
| insn_icmp _ _ _ v1 v2 => getValueIDs v1 ++ getValueIDs v2
| insn_fcmp _ _ _ v1 v2 => getValueIDs v1 ++ getValueIDs v2
| insn_select _ v0 _ v1 v2 => getValueIDs v0 ++ getValueIDs v1 ++ getValueIDs v2
| insn_call _ _ _ _ v0 lp => getValueIDs v0 ++ getParamsOperand lp
end.

Definition valueInListValue (v0:value) (vs:list_value) : Prop :=
In v0 (unmake_list_value vs).

Definition valueInParams (v0:value) (lp:params) : Prop :=
let '(_, vs) := split lp in In v0 vs.

Definition valueInCmdOperands (v0:value) (i:cmd) : Prop :=
match i with
| insn_bop _ _ _ v1 v2 => v0 = v1 \/ v0 = v2
| insn_fbop _ _ _ v1 v2 => v0 = v1 \/ v0 = v2
| insn_extractvalue _ _ v _ => v0 = v
| insn_insertvalue _ _ v1 _ v2 _ => v0 = v1 \/ v0 = v2
| insn_malloc _ _ v _ => v0 = v
| insn_free _ _ v => v0 = v
| insn_alloca _ _ v _ => v0 = v
| insn_load _ _ v _ => v0 = v
| insn_store _ _ v1 v2 _ => v0 = v1 \/ v0 = v2
| insn_gep _ _ _ v vs => v0 = v \/ valueInListValue v0 vs
| insn_trunc _ _ _ v _ => v0 = v
| insn_ext _ _ _ v1 _ => v0 = v1
| insn_cast _ _ _ v _ => v0 = v
| insn_icmp _ _ _ v1 v2 => v0 = v1 \/ v0 = v2
| insn_fcmp _ _ _ v1 v2 => v0 = v1 \/ v0 = v2
| insn_select _ v1 _ v2 v3 => v0 = v1 \/ v0 = v2 \/ v0 = v3
| insn_call _ _ _ _ v1 lp => v0 = v1 \/ valueInParams v0 lp
end.

Definition valueInTmnOperands (v0:value) (i:terminator) : Prop :=
match i with
| insn_return _ _ v => v = v0
| insn_return_void _ => False
| insn_br _ v _ _ => v = v0
| insn_br_uncond _ _ => False
| insn_unreachable _ => False
end.

Definition getTerminatorOperands (i:terminator) : ids :=
match i with
| insn_return _ _ v => getValueIDs v
| insn_return_void _ => nil
| insn_br _ v _ _ => getValueIDs v
| insn_br_uncond _ _ => nil
(* | insn_switch _ _ value _ _ => getValueIDs value *)
(* | insn_invoke _ _ _ lp _ _ => getParamsOperand lp *)
| insn_unreachable _ => nil
end.

Definition getPhiNodeOperands (i:phinode) : ids :=
match i with
| insn_phi _ _ ls => values2ids (list_prj1 _ _ (unmake_list_value_l ls))
end.

Definition getInsnOperands (i:insn) : ids :=
match i with
| insn_phinode p => getPhiNodeOperands p
| insn_cmd c => getCmdOperands c
| insn_terminator t => getTerminatorOperands t
end.

Definition getCmdLabels (i:cmd) : ls :=
match i with
| insn_bop _ _ _ _ _ => nil
| insn_fbop _ _ _ _ _ => nil
(* | insn_extractelement _ _ _ _ => nil
| insn_insertelement _ _ _ _ _ _ => nil
*)
| insn_extractvalue _ _ _ _ => nil
| insn_insertvalue _ _ _ _ _ _ => nil
| insn_malloc _ _ _ _ => nil
| insn_free _ _ _ => nil
| insn_alloca _ _ _ _ => nil
| insn_load _ _ _ _ => nil
| insn_store _ _ _ _ _ => nil
| insn_gep _ _ _ v  _ => nil
| insn_trunc _ _ _ _ _ => nil 
| insn_ext _ _ _ _ _ => nil
| insn_cast _ _ _ _ _ => nil
| insn_icmp _ _ _ _ _ => nil
| insn_fcmp _ _ _ _ _ => nil 
| insn_select _ _ _ _ _ => nil
| insn_call _ _ _ _ _ _ => nil
end.

Definition getTerminatorLabels (i:terminator) : ls :=
match i with
| insn_return _ _ _ => nil
| insn_return_void _ => nil
| insn_br _ _ l1 l2 => l1::l2::nil
| insn_br_uncond _ l => l::nil
(* | insn_switch _ _ _ l ls => l::list_prj2 _ _ ls *)
(* | insn_invoke _ _ _ _ l1 l2 => l1::l2::nil *)
| insn_unreachable _ => nil
end.

Definition getPhiNodeLabels (i:phinode) : ls :=
match i with
| insn_phi _ _ ls => list_prj2 _ _ (unmake_list_value_l ls)
end.

Definition getInsnLabels (i:insn) : ls :=
match i with
| insn_phinode p => getPhiNodeLabels p
| insn_cmd c => getCmdLabels c
| insn_terminator tmn => getTerminatorLabels tmn
end.

Fixpoint args2Typs (la:args) : list_typ :=
match la with
| nil => Nil_list_typ
| (t, _, id)::la' => Cons_list_typ t (args2Typs la')
end.

Definition getFheaderTyp (fh:fheader) : typ :=
match fh with
| fheader_intro _ t _ la va => typ_function t (args2Typs la) va
end.

Definition getFdecTyp (fdec:fdec) : typ :=
match fdec with
| fdec_intro fheader => getFheaderTyp fheader
end.

Definition getFdefTyp (fdef:fdef) : typ :=
match fdef with
| fdef_intro fheader _ => getFheaderTyp fheader
end.

Definition getBindingTyp (ib:id_binding) : option typ :=
match ib with
| id_binding_cmd i => getCmdTyp i
| id_binding_terminator i => Some (getTerminatorTyp i)
| id_binding_phinode i => Some (getPhiNodeTyp i)
| id_binding_gvar (gvar_intro _ _ _ t _ _) => Some (typ_pointer t)
| id_binding_gvar (gvar_external _ _ t) => Some (typ_pointer t)
| id_binding_arg (t, _, id) => Some t
| id_binding_fdec fdec => Some (getFdecTyp fdec)
| id_binding_none => None
end.

Definition getCmdsFromBlock (b:block) : cmds :=
match b with
| block_intro l _ li _ => li
(* | block_without_label li => li *)
end.

Definition getPhiNodesFromBlock (b:block) : phinodes :=
match b with
| block_intro l li _ _ => li
(* | block_without_label li => li *)
end.

Definition getTerminatorFromBlock (b:block) : terminator :=
match b with
| block_intro l _ _ t => t
(* | block_without_label li => li *)
end.

Definition getFheaderID (fh:fheader) : id :=
match fh with
| fheader_intro _ _ id _ _ => id
end.

Definition getFdecID (fd:fdec) : id :=
match fd with
| fdec_intro fh => getFheaderID fh
end.

Definition getFdefID (fd:fdef) : id :=
match fd with
| fdef_intro fh _ => getFheaderID fh
end.

Fixpoint getLabelViaIDFromList (ls:list_value_l) (branch:id) : option l :=
match ls with
| Nil_list_value_l => None
| Cons_list_value_l (value_id id) l ls' => 
  match (eq_dec id branch) with
  | left _ => Some l
  | right _ => getLabelViaIDFromList ls' branch
  end
| Cons_list_value_l _ l ls' => getLabelViaIDFromList ls' branch
end.

Definition getLabelViaIDFromPhiNode (phi:phinode) (branch:id) : option l :=
match phi with
| insn_phi _ _ ls => getLabelViaIDFromList ls branch
end.

Fixpoint getLabelsFromIdls (idls:list_value_l) : ls :=
match idls with
| Nil_list_value_l => lempty_set
| Cons_list_value_l _ l idls' => lset_add l (getLabelsFromIdls idls')
end.

Definition getLabelsFromPhiNode (phi:phinode) : ls :=
match phi with
| insn_phi _ _ ls => getLabelsFromIdls ls
end.

Fixpoint getLabelsFromPhiNodes (phis:list phinode) : ls :=
match phis with
| nil => lempty_set
| phi::phis' => lset_union (getLabelsFromPhiNode phi) (getLabelsFromPhiNodes phis')
end.

Definition getIDLabelsFromPhiNode p : list_value_l :=
match p with
| insn_phi _ _ idls => idls
end.

Fixpoint getLabelViaIDFromIDLabels idls id : option l :=
match idls with
| Nil_list_value_l => None
| Cons_list_value_l (value_id id0) l0 idls' => if eq_dec id id0 then Some l0 else getLabelViaIDFromIDLabels idls' id
| Cons_list_value_l _ l0 idls' => getLabelViaIDFromIDLabels idls' id
end.

Definition _getLabelViaIDPhiNode p id : option l :=
match p with
| insn_phi _ _ ls => getLabelViaIDFromIDLabels ls id
end.

Definition getLabelViaIDPhiNode (phi:insn) id : option l :=
match phi with
| insn_phinode p => _getLabelViaIDPhiNode p id
| _ => None
end.

Definition getReturnTyp fdef : typ :=
match fdef with
| fdef_intro (fheader_intro _ t _ _ _) _ => t
end.

Definition getGvarID g : id :=
match g with
| gvar_intro id _ _ _ _ _ => id
| gvar_external id _ _ => id
end.

Definition getCalledValue i : option value :=
match i with
| insn_cmd (insn_call _ _ _ _ v0 _) => Some v0
| _ => None
end.

Definition getCalledValueID i : option id :=
match getCalledValue i with
| Some v => getValueID v
| _ => None
end.

Definition getCallerReturnID (Caller:cmd) : option id :=
match Caller with
(* | insn_invoke i _ _ _ _ _ => Some i *)
| insn_call id true _ _ _ _ => None
| insn_call id false _ _ _ _ => Some id
| _ => None
end.

Fixpoint getValueViaLabelFromValuels (vls:list_value_l) (l0:l) : option value :=
match vls with
| Nil_list_value_l => None
| Cons_list_value_l v l1 vls'=>
  if (eq_dec l1 l0)
  then Some v
  else getValueViaLabelFromValuels vls' l0
end.

Definition getValueViaBlockFromValuels (vls:list_value_l) (b:block) : option value :=
match b with
| block_intro l _ _ _ => getValueViaLabelFromValuels vls l
end.

Definition getValueViaBlockFromPHINode (i:phinode) (b:block) : option value :=
match i with
| insn_phi _ _ vls => getValueViaBlockFromValuels vls b
end.

Definition getPHINodesFromBlock (b:block) : list phinode :=
match b with
| (block_intro _ lp _ _) => lp
end.

Definition getEntryBlock (fd:fdef) : option block :=
match fd with
| fdef_intro _ (b::_) => Some b
| _ => None
end.

Definition getEntryCmds (b:block) : cmds :=
match b with
| block_intro _ _ lc _ => lc
end.

Definition floating_point_order (fp1 fp2:floating_point) : bool :=
match (fp1, fp2) with
| (fp_float, fp_double) => true
| (fp_float, fp_x86_fp80) => true
| (fp_float, fp_ppc_fp128) => true
| (fp_float, fp_fp128) => true
| (fp_double, fp_x86_fp80) => true
| (fp_double, fp_ppc_fp128) => true
| (fp_double, fp_fp128) => true
| (fp_x86_fp80, fp_ppc_fp128) => true
| (fp_x86_fp80, fp_fp128) => true
| (_, _) => false
end.

Definition wf_fcond (fc : fcond) : bool :=
match fc with
| fcond_ord => false
| fcond_uno => false
| _ => true
end.

(**********************************)
(* Lookup. *)

(* ID binding lookup *)

Fixpoint lookupCmdViaIDFromCmds (li:cmds) (id0:id) : option cmd :=
match li with
| nil => None
| i::li' =>
    match (getCmdID i) with
    | Some id1 => 
        if (eq_atom_dec id0 id1) then Some i else lookupCmdViaIDFromCmds li' id0
    | Npne => None
    end
end.

Fixpoint lookupPhiNodeViaIDFromPhiNodes (li:phinodes) (id0:id) 
  : option phinode :=
match li with
| nil => None
| i::li' =>
    if (eq_dec (getPhiNodeID i) id0) then Some i 
    else lookupPhiNodeViaIDFromPhiNodes li' id0
end.

Definition lookupInsnViaIDFromBlock (b:block) (id:id) : option insn :=
match b with
| block_intro l ps cs t =>
  match (lookupPhiNodeViaIDFromPhiNodes ps id) with
  | None => 
      match (lookupCmdViaIDFromCmds cs id) with
      | None => None
      | Some c => Some (insn_cmd c)
      end
  | Some re => Some (insn_phinode re)    
  end
end.

Fixpoint lookupInsnViaIDFromBlocks (lb:blocks) (id:id) : option insn :=
match lb with
| nil => None
| b::lb' => 
  match (lookupInsnViaIDFromBlock b id) with
  | None => lookupInsnViaIDFromBlocks lb' id
  | re => re
  end
end.

Fixpoint lookupArgViaIDFromArgs (la:args) (id0:id) : option arg :=
match la with 
| nil => None
| (t, attrs, id')::la' => 
    if (eq_dec id' id0) then Some (t, attrs, id') 
    else lookupArgViaIDFromArgs la' id0
end.

(* Block lookup from ID *)

Fixpoint lookupBlockViaIDFromBlocks (lb:blocks) (id1:id) : option block :=
match lb with
| nil => None  
| b::lb' => 
  match (In_dec eq_dec id1 (getBlockIDs b)) with
  | left _ => Some b
  | right _ => lookupBlockViaIDFromBlocks lb' id1
  end
end.

Definition lookupBlockViaIDFromFdef (fd:fdef) (id:id) : option block :=
match fd with
| fdef_intro fh lb => lookupBlockViaIDFromBlocks lb id
end.

(* Fun lookup from ID *)

Definition lookupFdecViaIDFromProduct (p:product) (i:id) : option fdec :=
match p with
| (product_fdec fd) => if eq_dec (getFdecID fd) i then Some fd else None
| _ => None
end.

Fixpoint lookupFdecViaIDFromProducts (lp:products) (i:id) : option fdec :=
match lp with
| nil => None
| p::lp' => 
  match (lookupFdecViaIDFromProduct p i) with
  | Some fd => Some fd
  | None => lookupFdecViaIDFromProducts lp' i
  end
end.

Definition lookupFdecViaIDFromModule (m:module) (i:id) : option fdec :=
  let (os, dts, ps) := m in 
  lookupFdecViaIDFromProducts ps i.

Fixpoint lookupFdecViaIDFromModules (lm:modules) (i:id) : option fdec :=
match lm with
| nil => None
| m::lm' => 
  match (lookupFdecViaIDFromModule m i) with
  | Some fd => Some fd
  | None => lookupFdecViaIDFromModules lm' i
  end
end.

Definition lookupFdecViaIDFromSystem (s:system) (i:id) : option fdec :=
lookupFdecViaIDFromModules s i.

Definition lookupFdefViaIDFromProduct (p:product) (i:id) : option fdef :=
match p with
| (product_fdef fd) => if eq_dec (getFdefID fd) i then Some fd else None
| _ => None
end.

Fixpoint lookupFdefViaIDFromProducts (lp:products) (i:id) : option fdef :=
match lp with
| nil => None
| p::lp' => 
  match (lookupFdefViaIDFromProduct p i) with
  | Some fd => Some fd
  | None => lookupFdefViaIDFromProducts lp' i
  end
end.

Definition lookupFdefViaIDFromModule (m:module) (i:id) : option fdef :=
  let (os, dts, ps) := m in 
  lookupFdefViaIDFromProducts ps i.

Fixpoint lookupFdefViaIDFromModules (lm:modules) (i:id) : option fdef :=
match lm with
| nil => None
| m::lm' => 
  match (lookupFdefViaIDFromModule m i) with
  | Some fd => Some fd
  | None => lookupFdefViaIDFromModules lm' i
  end
end.

Definition lookupFdefViaIDFromSystem (s:system) (i:id) : option fdef :=
lookupFdefViaIDFromModules s i.

(*     ID type lookup                                    *)

Definition lookupTypViaIDFromCmd (i:cmd) (id0:id) : option typ :=
match (getCmdTyp i) with
| None => None
| Some t => 
  match (getCmdLoc i) with
  | id0' => 
    if (eq_dec id0 id0') 
    then Some t
    else None
  end
end.

Fixpoint lookupTypViaIDFromCmds (li:cmds) (id0:id) : option typ :=
match li with
| nil => None
| i::li' =>
  match (lookupTypViaIDFromCmd i id0) with
  | Some t => Some t
  | None => lookupTypViaIDFromCmds li' id0
  end
end.
    
Definition lookupTypViaIDFromPhiNode (i:phinode) (id0:id) : option typ :=
match (getPhiNodeTyp i) with
| t => 
  match (getPhiNodeID i) with
  | id0' => 
    if (eq_dec id0 id0') 
    then Some t
    else None
  end
end.

Fixpoint lookupTypViaIDFromPhiNodes (li:phinodes) (id0:id) : option typ :=
match li with
| nil => None
| i::li' =>
  match (lookupTypViaIDFromPhiNode i id0) with
  | Some t => Some t
  | None => lookupTypViaIDFromPhiNodes li' id0
  end
end.

Definition lookupTypViaIDFromTerminator (i:terminator) (id0:id) : option typ :=
match (getTerminatorTyp i) with
| t => 
  match (getTerminatorID i) with
  | id0' => 
    if (eq_dec id0 id0') 
    then Some t
    else None
  end
end.

Definition lookupTypViaIDFromBlock (b:block) (id0:id) : option typ :=
match b with
| block_intro l ps cs t =>
  match (lookupTypViaIDFromPhiNodes ps id0) with
  | None => 
    match (lookupTypViaIDFromCmds cs id0) with
    | None => lookupTypViaIDFromTerminator t id0
    | re => re
    end
  | re => re    
  end
end.

Fixpoint lookupTypViaIDFromBlocks (lb:blocks) (id0:id) : option typ :=
match lb with
| nil => None
| b::lb' =>
  match (lookupTypViaIDFromBlock b id0) with
  | Some t => Some t
  | None => lookupTypViaIDFromBlocks lb' id0
  end
end.

Fixpoint lookupTypViaIDFromArgs (la:args) (id0:id) : option typ :=
match la with
| nil => None
| (t1,_,id1)::la' => 
    if (id0==id1) then Some t1 else lookupTypViaIDFromArgs la' id0
end.

Definition lookupTypViaIDFromFdef (fd:fdef) (id0:id) : option typ :=
match fd with
| (fdef_intro (fheader_intro _ _ _ la _ ) lb) => 
    match lookupTypViaIDFromArgs la id0 with
    | None => lookupTypViaIDFromBlocks lb id0
    | Some t => Some t
    end
end.

Definition lookupTypViaGIDFromProduct (p:product) (id0:id) : option typ :=
match p with
| product_fdef fd => None
| product_gvar (gvar_intro id1 _ spec t _ _) => if id0==id1 then Some t else None
| product_gvar (gvar_external id1 spec t) => if id0==id1 then Some t else None
| _ => None
end.

Fixpoint lookupTypViaGIDFromProducts (lp:products) (id0:id) : option typ :=
match lp with
| nil => None
| p::lp' =>
  match (lookupTypViaGIDFromProduct p id0) with
  | Some t => Some t
  | None => lookupTypViaGIDFromProducts lp' id0
  end
end.

Definition lookupTypViaGIDFromModule (m:module) (id0:id) : option typ :=
  let (os, dts, ps) := m in  
  lookupTypViaGIDFromProducts ps id0.
     
Fixpoint lookupTypViaGIDFromModules (lm:modules) (id0:id) : option typ :=
match lm with
| nil => None
| m::lm' =>
  match (lookupTypViaGIDFromModule m id0) with
  | Some t => Some t
  | None => lookupTypViaGIDFromModules lm' id0
  end
end.

Definition lookupTypViaGIDFromSystem (s:system) (id0:id) : option typ :=
lookupTypViaGIDFromModules s id0.

Fixpoint lookupTypViaTIDFromNamedts (nts:namedts) (id0:id) : option typ :=
match nts with
| nil => None
| namedt_intro id1 typ1::nts' =>
  if (eq_dec id0 id1) 
  then Some typ1
  else lookupTypViaTIDFromNamedts nts' id0
end.

Definition lookupTypViaTIDFromModule (m:module) (id0:id) : option typ :=
  let (os, dts, ps) := m in  
  lookupTypViaTIDFromNamedts dts id0.
     
Fixpoint lookupTypViaTIDFromModules (lm:modules) (id0:id) : option typ :=
match lm with
| nil => None
| m::lm' =>
  match (lookupTypViaTIDFromModule m id0) with
  | Some t => Some t
  | None => lookupTypViaTIDFromModules lm' id0
  end
end.

Definition lookupTypViaTIDFromSystem (s:system) (id0:id) : option typ :=
lookupTypViaTIDFromModules s id0.

(**********************************)
(* labels <-> blocks. *)

  Definition l2block := list (l*block).

  Definition genLabel2Block_block (b:block) : l2block :=
  match b with
  | block_intro l _ _ _ => (l,b)::nil
  end.  

  Fixpoint genLabel2Block_blocks (bs:blocks) : l2block :=
  match bs with 
  | nil => nil
  | b::bs' => (genLabel2Block_block b)++(genLabel2Block_blocks bs')
  end.

  Definition genLabel2Block_fdef (f:fdef) : l2block := 
  match f with
  | fdef_intro fheader blocks => genLabel2Block_blocks blocks
  end.

  Fixpoint genLabel2Block_product (p:product) : l2block :=
  match p with 
  | product_gvar g => nil
  | product_fdef f => (genLabel2Block_fdef f)
  | product_fdec f => nil
  end.

  Fixpoint genLabel2Block_products (ps:products) : l2block :=
  match ps with
  | nil => nil
  | p::ps' => (genLabel2Block_product p)++(genLabel2Block_products ps')
  end.

  Definition genLabel2Block (m: module) : l2block :=
  let (os, dts, ps) := m in
  genLabel2Block_products ps.

  Definition getNonEntryOfFdef (f:fdef) : blocks :=
  match f with
  | fdef_intro fheader blocks => 
    match blocks with
    | nil => nil
    | b::blocks' => blocks'
    end 
  end.  

  Definition lookupBlockViaLabelFromBlocks (bs:blocks) (l0:l) : option block :=
  lookupAL _ (genLabel2Block_blocks bs) l0.

  Definition lookupBlockViaLabelFromFdef (f:fdef) (l0:l) : option block :=
  let '(fdef_intro _ bs) := f in
  lookupAL _ (genLabel2Block_fdef f) l0.
  
  Fixpoint getLabelsFromBlocks (lb:blocks) : ls :=
  match lb with
  | nil => lempty_set
  | (block_intro l0 _ _ _)::lb' => lset_add l0 (getLabelsFromBlocks lb')
  end.

(**********************************)
(* generate block use-def *)

  Definition update_udb (udb:usedef_block) (lu ld:l) : usedef_block :=
  let ls :=
    match lookupAL _ udb ld with
    | Some ls => ls
    | None => nil
    end in
  match (in_dec l_dec lu ls) with
  | left _ => udb
  | right _ => updateAddAL _ udb ld (lu::ls) 
  end.

  Definition genBlockUseDef_block b (udb:usedef_block) : usedef_block :=
  match b with
  | block_intro l0 _ _ tmn2 =>
    match tmn2 with
    | insn_br _ _ l1 l2 => update_udb (update_udb udb l0 l2) l0 l1
    | insn_br_uncond _ l1 => update_udb udb l0 l1
    | _ => udb
    end
  end.

  Fixpoint genBlockUseDef_blocks bs (udb:usedef_block) : usedef_block :=
  match bs with
  | nil => udb
  | b::bs' => genBlockUseDef_blocks bs' (genBlockUseDef_block b udb)
  end.

  Definition genBlockUseDef_fdef f2 : usedef_block :=
  match f2 with
  | fdef_intro _ lb2 => genBlockUseDef_blocks lb2 nil
  end.

  Definition getBlockLabel (b:block) : l :=
  match b with
  | block_intro l _ _ _ => l
  end.

  Definition getBlockUseDef (udb:usedef_block) (b:block) : option (list l) :=
  lookupAL _ udb (getBlockLabel b).

(**********************************)
(* CFG. *)

  Definition getTerminator (b:block) : terminator := 
  match b with
  | block_intro l _ _ t => t
  end. 

  Fixpoint getLabelsFromSwitchCases (cs:list (const*l)) : ls :=
  match cs with
  | nil => lempty_set 
  | (_, l0)::cs' => lset_add l0 (getLabelsFromSwitchCases cs')
  end.

  Definition getLabelsFromTerminator (i:terminator) : ls := 
  match i with
  | insn_br _ v l1 l2 => lset_add l1 (lset_add l2 lempty_set)
  | insn_br_uncond _ l0 => lset_add l0 lempty_set 
  (* | insn_switch _ t v l0 cls => lset_add l0 (getLabelsFromSwitchCases cls) *)
  (* | insn_invoke id typ id0 ps l1 l2 => lset_add l1 (lset_add l2 lempty_set) *)
  | _ => empty_set l
  end.

  Fixpoint getBlocksFromLabels (ls0:ls) (l2b:l2block): blocks :=
  match ls0 with
  | nil => nil
  | l0::ls0' => 
    match (lookupAL _ l2b l0) with
    | None => getBlocksFromLabels ls0' l2b
    | Some b => b::getBlocksFromLabels ls0' l2b
    end
  end.

  Definition succOfBlock (b:block) (m:module) : blocks :=
  match (getTerminator b) with
  | i => getBlocksFromLabels (getLabelsFromTerminator i) (genLabel2Block m)
  end.
  
  Definition predOfBlock (b:block) (udb:usedef_block) : list l :=
  match (lookupAL _ udb (getBlockLabel b)) with
  | None => nil
  | Some re => re
  end.

  Definition hasSinglePredecessor (b:block) (udb:usedef_block) : bool :=
  match predOfBlock b udb with
  | _::nil => true
  | _ => false
  end.

  Definition hasNonePredecessor (b:block) (udb:usedef_block) : bool :=
  match predOfBlock b udb with
  | nil => true
  | _ => false
  end.

  Definition successors_terminator (tmn: terminator) : ls :=
  match tmn with
  | insn_return _ _ _ => nil
  | insn_return_void _ => nil
  | insn_br _ _ l1 l2 => l1::l2::nil
  | insn_br_uncond _ l1 => l1::nil
  | insn_unreachable _ => nil
  end.

(**********************************)
(* Classes. *)

Definition isPointerTypB (t:typ) : bool :=
match t with
| typ_pointer _ => true
| _ => false
end.

Definition isFunctionPointerTypB (t:typ) : bool :=
match t with
| typ_pointer (typ_function _ _ _) => true
| _ => false
end.

Definition isArrayTypB (t:typ) : bool :=
match t with
| typ_array _ _ => true
| _ => false
end.

(*
Definition isInvokeInsnB (i:insn) : bool :=
match i with
| insn_invoke _ _ _ _ _ _ => true
| _ => false
end.
*)

Definition isReturnInsnB (i:terminator) : bool :=
match i with
| insn_return _ _ _ => true
| insn_return_void _ => true
| _ => false
end.

Definition _isCallInsnB (i:cmd) : bool :=
match i with
| insn_call _ _ _ _ _ _ => true
| _ => false
end.

Definition isCallInsnB (i:insn) : bool :=
match i with
| insn_cmd c => _isCallInsnB c
| _ => false
end.

Definition isNotValidReturnTypB (t:typ) : bool :=
match t with
| typ_label => true
| typ_metadata => true
| _ => false
end.

Definition isValidReturnTypB (t:typ) : bool :=
negb (isNotValidReturnTypB t).

Definition isNotFirstClassTypB (t:typ) : bool :=
match t with
| typ_void => true
(* | typ_opaque => true *)
| typ_function _ _ _ => true
| _ => false
end.

Definition isFirstClassTypB (t:typ) : bool :=
negb (isNotFirstClassTypB t).

Definition isValidArgumentTypB (t:typ) : bool :=
match t with
(*| typ_opaque => true *)
| _ => isFirstClassTypB t
end.

Definition isNotValidElementTypB (t:typ) : bool :=
match t with
| typ_void => true
| typ_label => true
| typ_metadata => true
| typ_function _ _ _ => true
| _ => false
end.

Definition isValidElementTypB (t:typ) : bool :=
negb (isNotValidElementTypB t).

Definition isBindingFdecB (ib:id_binding) : bool :=
match ib with
| id_binding_fdec fdec => true
| _ => false
end.

Definition isBindingGvarB (ib:id_binding) : bool :=
match ib with
| id_binding_gvar _ => true
| _ => false
end.

Definition isBindingArgB (ib:id_binding) : bool :=
match ib with
| id_binding_arg arg => true
| _ => false
end.

Definition isBindingCmdB (ib:id_binding) : bool :=
match ib with
| id_binding_cmd _ => true
| _ => false
end.

Definition isBindingTerminatorB (ib:id_binding) : bool :=
match ib with
| id_binding_terminator _ => true
| _ => false
end.

Definition isBindingPhiNodeB (ib:id_binding) : bool :=
match ib with
| id_binding_phinode _ => true
| _ => false
end.

Definition isBindingInsnB (ib:id_binding) : bool :=
isBindingCmdB ib || isBindingTerminatorB ib || isBindingPhiNodeB ib.

Definition isPointerTyp typ := isPointerTypB typ = true.

Definition isFunctionPointerTyp t := isFunctionPointerTypB t = true.

(* Definition isInvokeInsn insn := isInvokeInsnB insn = true. *)

Definition isReturnTerminator tmn := isReturnInsnB tmn = true.

Definition isNotValidReturnTyp typ := isNotValidReturnTypB typ = true.
      
Definition isValidReturnTyp typ := isValidReturnTypB typ = true.

Definition isNotFirstClassTyp typ := isNotFirstClassTypB typ = true.

Definition isFirstClassTyp typ := isFirstClassTypB typ = true.

Definition isValidArgumentTyp typ := isValidArgumentTypB typ = true.

Definition isNotValidElementTyp typ := isNotValidElementTypB typ = true.

Definition isValidElementTyp typ := isValidElementTypB typ = true.

Definition isBindingFdec ib : option fdec :=
match ib with
| id_binding_fdec f => Some f
| _ => None
end.

Definition isBindingArg ib : option arg :=
match ib with
| id_binding_arg a => Some a
| _ => None
end.

Definition isBindingGvar ib : option gvar :=
match ib with
| id_binding_gvar g => Some g
| _ => None
end.

Definition isBindingCmd ib : option cmd :=
match ib with
| id_binding_cmd c => Some c
| _ => None
end.

Definition isBindingPhiNode ib : option phinode :=
match ib with
| id_binding_phinode p => Some p
| _ => None
end.

Definition isBindingTerminator ib : option terminator :=
match ib with
| id_binding_terminator tmn => Some tmn
| _ => None
end.

Definition isBindingInsn ib : option insn :=
match ib with
| id_binding_cmd c => Some (insn_cmd c)
| id_binding_phinode p => Some (insn_phinode p)
| id_binding_terminator tmn => Some (insn_terminator tmn)
| _ => None
end.

Definition isAggregateTyp t := 
match t with
| typ_struct _ => True
| typ_array _ _ => True 
| _ => False
end.

(*************************************************)
(*         Uniq                                  *)

Fixpoint getCmdsLocs (cs:list cmd) : ids :=
match cs with
| nil => nil
| c::cs' => getCmdLoc c::getCmdsLocs cs'
end.

Definition getBlockLocs b : ids :=
match b with
| block_intro l ps cs t =>
  getPhiNodesIDs ps++getCmdsLocs cs++(getTerminatorID t::nil)
end.

Fixpoint getBlocksLocs bs : ids :=
match bs with
| nil => nil
| b::bs' => getBlockLocs b++getBlocksLocs bs'
end.

Fixpoint getBlocksLabels bs : ls :=
match bs with
| nil => nil
| (block_intro l _ _ _)::bs' => l::getBlocksLabels bs'
end.

Definition uniqBlocks bs : Prop :=
let ls := getBlocksLabels bs in
let ids := getBlocksLocs bs in
NoDup ls /\ NoDup ids.

Definition uniqFdef fdef : Prop :=
match fdef with
| (fdef_intro (fheader_intro _ _ _ la _) bs) => 
    uniqBlocks bs /\ NoDup (getArgsIDs la ++ getBlocksLocs bs)
end.

Definition getProductID product : id :=
match product with
| product_gvar g => getGvarID g
| product_fdec f => getFdecID f
| product_fdef f => getFdefID f
end.

Fixpoint getProductsIDs ps : ids :=
match ps with
| nil => nil
| p::ps' => getProductID p::getProductsIDs ps'
end.
   
Definition uniqProduct product : Prop :=
match product with
| product_gvar g => True
| product_fdec f => True
| product_fdef f => uniqFdef f
end.

Fixpoint uniqProducts ps : Prop :=
match ps with
| nil => True
| p::ps' => uniqProduct p /\ uniqProducts ps'
end.

Fixpoint getNamedtsIDs dts : ids :=
match dts with
| nil => nil
| namedt_intro id0 _::dts' => id0::getNamedtsIDs dts'
end.

Definition uniqModule m : Prop :=
match m with
| module_intro _ dts ps => uniqProducts ps /\ 
                           NoDup (getNamedtsIDs dts) /\
                           NoDup (getProductsIDs ps)
end.

Fixpoint uniqModules ms : Prop :=
match ms with
| nil => True
| m::ms' => uniqModule m /\ uniqModules ms'
end.

Definition uniqSystem s : Prop := uniqModules s.

(**********************************)
(* Dec. *)

Definition sumbool2bool A B (dec:sumbool A B) : bool :=
match dec with
| left _ => true
| right _ => false
end.

Lemma sumbool2bool_true : forall A B H,
  sumbool2bool A B H = true -> A.
Proof.
  intros.
  unfold sumbool2bool in H0.
  destruct H; auto.
    inversion H0.
Qed.

Lemma sumbool2bool_false : forall A B H,
  sumbool2bool A B H = false -> B.
Proof.
  intros.
  unfold sumbool2bool in H0.
  destruct H; auto.
    inversion H0.
Qed.

Lemma eq_sumbool2bool_true : forall A (a1 a2:A) (H:{a1=a2}+{~a1=a2}),
  a1 = a2 ->
  sumbool2bool _ _ H = true.
Proof.
  intros; subst.
  destruct H; auto.
Qed.

Lemma floating_point_dec : forall (fp1 fp2:floating_point), {fp1=fp2}+{~fp1=fp2}.
Proof.
  decide equality.
Qed.

Definition typ_dec_prop (t1:typ) := forall t2, {t1=t2} + {~t1=t2}.
Definition list_typ_dec_prop (lt1:list_typ) := forall lt2, {lt1=lt2} + {~lt1=lt2}.

Ltac done_right := right; intro J; inversion J; subst; auto.

Lemma typ_mutrec_dec :
  (forall t1, typ_dec_prop t1) *
  (forall lt1, list_typ_dec_prop lt1).
Proof.
  apply typ_mutrec; 
    unfold typ_dec_prop, list_typ_dec_prop;
    intros;
    try solve [
      destruct t2; try solve [done_right | auto]
    ].

  destruct t2; try solve [done_right].
  destruct (@Size.dec s s0); try solve [subst; auto | done_right].

  destruct t2; try solve [done_right].
  destruct (@floating_point_dec f f0); try solve [subst; auto | done_right].

  destruct t2; try solve [done_right].
  destruct (@H t2); subst; try solve [done_right].
  destruct (@Size.dec s s0); subst; try solve [subst; auto | done_right].

  destruct t2; try solve [done_right].
  destruct (@H t2); subst; try solve [done_right].
  destruct (@varg_dec v v0); subst; try solve [done_right].
  destruct (@H0 l1); subst; try solve [subst; auto | done_right].

  destruct t2; try solve [done_right].
  destruct (@H l1); subst; try solve [subst; auto | done_right].

  destruct t2; try solve [done_right].
  destruct (@H t2); subst; try solve [subst; auto | done_right].

  destruct t2; try solve [done_right].
  destruct (@id_dec i0 i1); try solve [subst; auto | done_right].

  destruct lt2; try solve [auto | done_right].

  destruct lt2; try solve [right; intro J; inversion J].
  destruct (@H t0); subst; try solve [done_right].
  destruct (@H0 lt2); subst; try solve [subst; auto | done_right].
Qed.

Lemma typ_dec : forall (t1 t2:typ), {t1=t2} + {~t1=t2}.
Proof.
  destruct typ_mutrec_dec; auto.
Qed.

Lemma list_typ_dec : forall (lt1 lt2:list_typ), {lt1=lt2} + {~lt1=lt2}.
Proof.
  destruct typ_mutrec_dec; auto.
Qed.

Lemma bop_dec : forall (b1 b2:bop), {b1=b2}+{~b1=b2}.
Proof.
  decide equality.
Qed.

Lemma fbop_dec : forall (b1 b2:fbop), {b1=b2}+{~b1=b2}.
Proof.
  decide equality.
Qed.

Lemma extop_dec : forall (e1 e2:extop), {e1=e2}+{~e1=e2}.
Proof.
  decide equality.
Qed.

Lemma castop_dec : forall (c1 c2:castop), {c1=c2}+{~c1=c2}.
Proof.
  decide equality.
Qed.

Lemma cond_dec : forall (c1 c2:cond), {c1=c2}+{~c1=c2}.
Proof.
  decide equality.
Qed.

Lemma fcond_dec : forall (c1 c2:fcond), {c1=c2}+{~c1=c2}.
Proof.
  decide equality.
Qed.

Lemma truncop_dec : forall (t1 t2:truncop), {t1=t2}+{~t1=t2}.
Proof.
  decide equality.
Qed.

Definition const_dec_prop (c1:const) := forall c2, {c1=c2} + {~c1=c2}.
Definition list_const_dec_prop (lc1:list_const) := forall lc2, {lc1=lc2} + {~lc1=lc2}.

Lemma const_mutrec_dec :
  (forall c1, const_dec_prop c1) *
  (forall lc1, list_const_dec_prop lc1).
Proof.
  apply const_mutrec; 
    unfold const_dec_prop, list_const_dec_prop;
    intros;
    try solve [
      destruct c2; try solve [right; intro J; inversion J | auto] |
      destruct c2; try solve [done_right];
        destruct (@typ_dec t t0); subst; try solve [subst; auto | done_right] |
      destruct c2; try solve [done_right];
        destruct (@H l1); subst; try solve [auto | done_right]
    ].

  destruct c2; try solve [done_right].
  destruct (@INTEGER.dec i0 i1); try solve [done_right].
  destruct (@Size.dec s s0); try solve [subst; auto | done_right].

  destruct c2; try solve [done_right].
  destruct (@FLOAT.dec f0 f2); try solve [done_right].
  destruct (@floating_point_dec f f1); try solve [subst; auto | done_right].

  destruct c2; try solve [done_right].
  destruct (@typ_dec t t0); subst; try solve [done_right].
  destruct (@H l1); subst; try solve [subst; auto | done_right].

  destruct c2; try solve [done_right].
  destruct (@typ_dec t t0); subst; try solve [done_right].
  destruct (@id_dec i0 i1); try solve [subst; auto | done_right].

  destruct c2; try solve [done_right].
  destruct (@truncop_dec t t1); subst; try solve [done_right].
  destruct (@typ_dec t0 t2); subst; try solve [done_right].
  destruct (@H c2); subst; try solve [subst; auto | done_right].

  destruct c2; try solve [done_right].
  destruct (@extop_dec e e0); subst; try solve [done_right].
  destruct (@typ_dec t t0); subst; try solve [done_right].
  destruct (@H c2); subst; try solve [subst; auto | done_right].

  destruct c2; try solve [done_right].
  destruct (@castop_dec c c1); subst; try solve [done_right].
  destruct (@typ_dec t t0); subst; try solve [done_right].
  destruct (@H c2); subst; try solve [subst; auto | done_right].

  destruct c2; try solve [done_right].
  destruct (@inbounds_dec i0 i1); subst; try solve [done_right].
  destruct (@H c2); subst; try solve [done_right].
  destruct (@H0 l1); subst; try solve [subst; auto | done_right].

  destruct c2; try solve [done_right].
  destruct (@H c2_1); subst; try solve [done_right].
  destruct (@H0 c2_2); subst; try solve [done_right].
  destruct (@H1 c2_3); subst; try solve [subst; auto | done_right].

  destruct c2; try solve [done_right].
  destruct (@cond_dec c c2); subst; try solve [done_right].
  destruct (@H c2_1); subst; try solve [done_right].
  destruct (@H0 c2_2); subst; try solve [subst; auto | done_right].

  destruct c2; try solve [done_right].
  destruct (@fcond_dec f f0); subst; try solve [done_right].
  destruct (@H c2_1); subst; try solve [done_right].
  destruct (@H0 c2_2); subst; try solve [subst; auto | done_right].

  destruct c2; try solve [done_right].
  destruct (@H c2); subst; try solve [done_right].
  destruct (@H0 l1); subst; try solve [subst; auto | done_right].

  destruct c2; try solve [done_right].
  destruct (@H c2_1); subst; try solve [done_right].
  destruct (@H0 c2_2); subst; try solve [done_right].
  destruct (@H1 l1); subst; try solve [subst; auto | done_right].

  destruct c2; try solve [done_right].
  destruct (@bop_dec b b0); subst; try solve [done_right].
  destruct (@H c2_1); subst; try solve [done_right].
  destruct (@H0 c2_2); subst; try solve [subst; auto | done_right].

  destruct c2; try solve [done_right].
  destruct (@fbop_dec f f0); subst; try solve [done_right].
  destruct (@H c2_1); subst; try solve [done_right].
  destruct (@H0 c2_2); subst; try solve [subst; auto | done_right].

  destruct lc2; try solve [auto | done_right].

  destruct lc2; try solve [done_right].
  destruct (@H c0); subst; try solve [done_right].
  destruct (@H0 lc2); subst; try solve [subst; auto | done_right].
Qed.

Lemma const_dec : forall (c1 c2:const), {c1=c2}+{~c1=c2}.
Proof.
  destruct const_mutrec_dec; auto.
Qed.

Lemma list_const_dec : forall (lc1 lc2:list_const), {lc1=lc2} + {~lc1=lc2}.
Proof.
  destruct const_mutrec_dec; auto.
Qed.

Lemma value_dec : forall (v1 v2:value), {v1=v2}+{~v1=v2}.
Proof.
  decide equality.
    destruct (@const_dec c c0); subst; auto.
Qed.    

Lemma params_dec : forall (p1 p2:params), {p1=p2}+{~p1=p2}.
Proof.
  decide equality.
    destruct a. destruct p.
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@value_dec v v0); subst; try solve [auto | done_right].
Qed.

Lemma list_value_l_dec : forall (l1 l2:list_value_l), {l1=l2}+{~l1=l2}.
Proof.
  induction l1.
    destruct l2; subst; try solve [subst; auto | done_right].

    destruct l2; subst; try solve [done_right].
    destruct (@value_dec v v0); subst; try solve [done_right].
    destruct (@l_dec l0 l2); subst; try solve [done_right].
    destruct (@IHl1 l3); subst; try solve [auto | done_right].
Qed.

Lemma list_value_dec : forall (lv1 lv2:list_value), {lv1=lv2}+{~lv1=lv2}.
Proof.
  decide equality.
    destruct (@value_dec v v0); subst; try solve [auto | done_right].
Qed.

Lemma callconv_dec : forall (cc1 cc2:callconv), {cc1=cc2}+{~cc1=cc2}.
Proof.
  decide equality.
Qed.

Lemma attribute_dec : forall (attr1 attr2:attribute), 
  {attr1=attr2}+{~attr1=attr2}.
Proof.
  decide equality.
Qed.

Lemma attributes_dec : forall (attrs1 attrs2:attributes), 
  {attrs1=attrs2}+{~attrs1=attrs2}.
Proof.
  decide equality.
    destruct (@attribute_dec a a0); subst; try solve [auto | done_right].
Qed.

Lemma cmd_dec : forall (c1 c2:cmd), {c1=c2}+{~c1=c2}.
Proof.
  (cmd_cases (destruct c1) Case); destruct c2; try solve [done_right | auto].
  Case "insn_bop".
    destruct (@id_dec i0 i1); subst; try solve [done_right]. 
    destruct (@bop_dec b b0); subst; try solve [done_right].
    destruct (@Size.dec s s0); subst; try solve [done_right].
    destruct (@value_dec v v1); subst; try solve [done_right].
    destruct (@value_dec v0 v2); subst; try solve [auto | done_right].
  Case "insn_fbop".
    destruct (@id_dec i0 i1); subst; try solve [done_right]. 
    destruct (@fbop_dec f f1); subst; try solve [done_right].
    destruct (@floating_point_dec f0 f2); subst; try solve [done_right].
    destruct (@value_dec v v1); subst; try solve [done_right].
    destruct (@value_dec v0 v2); subst; try solve [auto | done_right].
  Case "insn_extractvalue".
    destruct (@id_dec i0 i1); subst; try solve [done_right]. 
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@value_dec v v0); subst; try solve [done_right].
    destruct (@list_const_dec l0 l1); subst; try solve [auto | done_right].
  Case "insn_insertvalue".
    destruct (@id_dec i0 i1); subst; try solve [done_right]. 
    destruct (@typ_dec t t1); subst; try solve [done_right].
    destruct (@value_dec v v1); subst; try solve [done_right].
    destruct (@typ_dec t0 t2); subst; try solve [done_right].
    destruct (@value_dec v0 v2); subst; try solve [done_right].
    destruct (@list_const_dec l0 l1); subst; try solve [auto | done_right].
  Case "insn_malloc".    
    destruct (@id_dec i0 i1); subst; try solve [done_right]. 
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@value_dec v v0); subst; try solve [done_right].
    destruct (@Align.dec a a0); subst; try solve [auto | done_right].
  Case "insn_free".    
    destruct (@id_dec i0 i1); subst; try solve [done_right]. 
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@value_dec v v0); subst; try solve [auto | done_right].
  Case "insn_alloca".    
    destruct (@id_dec i0 i1); subst; try solve [done_right]. 
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@value_dec v v0); subst; try solve [done_right].
    destruct (Align.dec a a0); subst; try solve [auto | done_right].
  Case "insn_load".    
    destruct (@id_dec i0 i1); subst; try solve [done_right]. 
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@Align.dec a a0); subst; try solve [done_right].
    destruct (@value_dec v v0); subst; try solve [auto | done_right].
  Case "insn_store".    
    destruct (@id_dec i0 i1); subst; try solve [done_right]. 
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@value_dec v v1); try solve [auto | done_right].
    destruct (@Align.dec a a0); subst; try solve [done_right].
    destruct (@value_dec v0 v2); subst; try solve [auto | done_right].
  Case "insn_gep".    
    destruct (@id_dec i0 i2); subst; try solve [done_right]. 
    destruct (@inbounds_dec i1 i3); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@value_dec v v0); try solve [auto | done_right].
    destruct (@list_value_dec l0 l1); subst; try solve [auto | done_right].
  Case "insn_trunc".
    destruct (@id_dec i0 i1); subst; try solve [done_right]. 
    destruct (@truncop_dec t t2); subst; try solve [done_right].
    destruct (@typ_dec t0 t3); subst; try solve [done_right].
    destruct (@value_dec v v0); subst; try solve [done_right].
    destruct (@typ_dec t1 t4); subst; try solve [auto | done_right].
  Case "insn_ext".
    destruct (@id_dec i0 i1); subst; try solve [done_right]. 
    destruct (@extop_dec e e0); subst; try solve [done_right].
    destruct (@typ_dec t t1); subst; try solve [done_right].
    destruct (@value_dec v v0); subst; try solve [done_right].
    destruct (@typ_dec t0 t2); subst; try solve [auto | done_right].
  Case "insn_cast".
    destruct (@id_dec i0 i1); subst; try solve [done_right]. 
    destruct (@castop_dec c c0); subst; try solve [done_right].
    destruct (@typ_dec t t1); subst; try solve [done_right].
    destruct (@value_dec v v0); subst; try solve [done_right].
    destruct (@typ_dec t0 t2); subst; try solve [auto | done_right].
  Case "insn_icmp".
    destruct (@id_dec i0 i1); subst; try solve [done_right]. 
    destruct (@cond_dec c c0); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@value_dec v v1); subst; try solve [done_right].
    destruct (@value_dec v0 v2); subst; try solve [auto | done_right].
  Case "insn_fcmp".
    destruct (@id_dec i0 i1); subst; try solve [done_right]. 
    destruct (@fcond_dec f f1); subst; try solve [done_right].
    destruct (@floating_point_dec f0 f2); subst; try solve [done_right].
    destruct (@value_dec v v1); subst; try solve [done_right].
    destruct (@value_dec v0 v2); subst; try solve [auto | done_right].
  Case "insn_select".
    destruct (@id_dec i0 i1); subst; try solve [done_right]. 
    destruct (@value_dec v v2); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@value_dec v0 v3); subst; try solve [done_right].
    destruct (@value_dec v1 v4); subst; try solve [auto | done_right].
  Case "insn_call".
    destruct (@id_dec i0 i1); subst; try solve [done_right]. 
    destruct (@value_dec v v0); subst; try solve [done_right]. 
    destruct (@noret_dec n n0); subst; try solve [done_right].
    destruct c. destruct c0.
    destruct (@tailc_dec t1 t2); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@callconv_dec c c0); subst; try solve [done_right]. 
    destruct (@attributes_dec a a1); subst; try solve [done_right]. 
    destruct (@attributes_dec a0 a2); subst; try solve [done_right]. 
    destruct (@params_dec p p0); subst; try solve [auto | done_right].
Qed.

Lemma terminator_dec : forall (tmn1 tmn2:terminator), {tmn1=tmn2}+{~tmn1=tmn2}.
Proof.
  destruct tmn1; destruct tmn2; try solve [done_right | auto].
  Case "insn_return".
    destruct (@id_dec i0 i1); subst; try solve [done_right]. 
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@value_dec v v0); subst; try solve [auto | done_right].
  Case "insn_return_void".
    destruct (@id_dec i0 i1); subst; try solve [auto | done_right]. 
  Case "insn_br".
    destruct (@id_dec i0 i1); subst; try solve [done_right]. 
    destruct (@l_dec l0 l2); subst; try solve [done_right]. 
    destruct (@l_dec l1 l3); subst; try solve [done_right]. 
    destruct (@value_dec v v0); subst; try solve [auto | done_right].
  Case "insn_br_uncond".
    destruct (@id_dec i0 i1); subst; try solve [done_right]. 
    destruct (@l_dec l0 l1); subst; try solve [auto | done_right]. 
  Case "insn_unreachable".
    destruct (@id_dec i0 i1); subst; try solve [auto | done_right]. 
Qed.

Lemma phinode_dec : forall (p1 p2:phinode), {p1=p2}+{~p1=p2}.
Proof.
  destruct p1; destruct p2; try solve [done_right | auto].
    destruct (@id_dec i0 i1); subst; try solve [done_right]. 
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@list_value_l_dec l0 l1); subst; try solve [auto | done_right]. 
Qed.

Lemma insn_dec : forall (i1 i2:insn), {i1=i2}+{~i1=i2}.
Proof.
  destruct i1; destruct i2; try solve [done_right | auto].
    destruct (@phinode_dec p p0); subst; try solve [auto | done_right]. 
    destruct (@cmd_dec c c0); subst; try solve [auto | done_right]. 
    destruct (@terminator_dec t t0); subst; try solve [auto | done_right]. 
Qed.

Lemma cmds_dec : forall (cs1 cs2:list cmd), {cs1=cs2}+{~cs1=cs2}.
Proof.
  induction cs1.
    destruct cs2; subst; try solve [subst; auto | done_right].

    destruct cs2; subst; try solve [done_right].
    destruct (@cmd_dec a c); subst; try solve [done_right].
    destruct (@IHcs1 cs2); subst; try solve [auto | done_right].
Qed.

Lemma phinodes_dec : forall (ps1 ps2:list phinode), {ps1=ps2}+{~ps1=ps2}.
Proof.
  induction ps1.
    destruct ps2; subst; try solve [subst; auto | done_right].

    destruct ps2; subst; try solve [done_right].
    destruct (@phinode_dec a p); subst; try solve [done_right].
    destruct (@IHps1 ps2); subst; try solve [auto | done_right].
Qed.

Lemma block_dec : forall (b1 b2:block), {b1=b2}+{~b1=b2}.
Proof.
  destruct b1; destruct b2; try solve [done_right | auto].
    destruct (@id_dec l0 l1); subst; try solve [done_right]. 
    destruct (@phinodes_dec p p0); subst; try solve [done_right]. 
    destruct (@cmds_dec c c0); subst; try solve [done_right].
    destruct (@terminator_dec t t0); subst; try solve [auto | done_right]. 
Qed.

Lemma arg_dec : forall (a1 a2:arg), {a1=a2}+{~a1=a2}.
Proof.
  destruct a1; destruct a2; try solve [subst; auto | done_right].
    destruct (@id_dec i0 i1); subst; try solve [done_right].
    destruct p. destruct p0.
    destruct (@attributes_dec a a0); subst; try solve [done_right]. 
    destruct (@typ_dec t t0); subst; try solve [auto | done_right].
Qed.  

Lemma args_dec : forall (l1 l2:args), {l1=l2}+{~l1=l2}.
Proof.
  induction l1.
    destruct l2; subst; try solve [subst; auto | done_right].

    destruct l2; subst; try solve [done_right].
    destruct (@arg_dec a p); subst; try solve [done_right].
    destruct (@IHl1 l2); subst; try solve [auto | done_right].
Qed.

Lemma visibility_dec : forall (vb1 vb2:visibility), {vb1=vb2}+{~vb1=vb2}.
Proof.
  decide equality.
Qed.

Lemma linkage_dec : forall (lk1 lk2:linkage), {lk1=lk2}+{~lk1=lk2}.
Proof.
  decide equality.
Qed.

Lemma fheader_dec : forall (f1 f2:fheader), {f1=f2}+{~f1=f2}.
Proof.
  destruct f1; destruct f2; try solve [subst; auto | done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@id_dec i0 i1); subst; try solve [done_right].
    destruct f. destruct f0.
    destruct (@visibility_dec v1 v2); subst; try solve [done_right].
    destruct (@varg_dec v v0); subst; try solve [done_right].
    destruct (@attributes_dec a1 a3); subst; try solve [done_right]. 
    destruct (@attributes_dec a2 a4); subst; try solve [done_right]. 
    destruct (@callconv_dec c c0); subst; try solve [done_right].
    destruct (@linkage_dec l0 l1); subst; try solve [done_right].
    destruct (@args_dec a a0); subst; try solve [auto | done_right].
Qed.  

Lemma blocks_dec : forall (lb lb':blocks), {lb=lb'}+{~lb=lb'}.
Proof.
  induction lb.
    destruct lb'; subst; try solve [subst; auto | done_right].

    destruct lb'; subst; try solve [done_right].
    destruct (@block_dec a b); subst; try solve [done_right].
    destruct (@IHlb lb'); subst; try solve [auto | done_right].
Qed.

Lemma fdec_dec : forall (f1 f2:fdec), {f1=f2}+{~f1=f2}.
Proof.
  destruct f1; destruct f2; try solve [subst; auto | done_right].
    destruct (@fheader_dec f f0); subst; try solve [auto | done_right].
Qed.  

Lemma fdef_dec : forall (f1 f2:fdef), {f1=f2}+{~f1=f2}.
Proof.
  destruct f1; destruct f2; try solve [subst; auto | done_right].
    destruct (@fheader_dec f f0); subst; try solve [done_right].
    destruct (@blocks_dec b b0); subst; try solve [auto | done_right].
Qed.  

Lemma gvar_spec_dec : forall (g1 g2:gvar_spec), {g1=g2}+{~g1=g2}.
Proof.
  decide equality.
Qed.

Lemma gvar_dec : forall (g1 g2:gvar), {g1=g2}+{~g1=g2}.
Proof.
  destruct g1; destruct g2; try solve [subst; auto | done_right].
    destruct (@id_dec i0 i1); subst; try solve [done_right].
    destruct (@linkage_dec l0 l1); subst; try solve [done_right].
    destruct (@gvar_spec_dec g g0); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@const_dec c c0); subst; try solve [done_right].
    destruct (@Align.dec a a0); subst; try solve [auto | done_right].

    destruct (@id_dec i0 i1); subst; try solve [done_right].
    destruct (@gvar_spec_dec g g0); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [auto | done_right].
Qed.  

Lemma product_dec : forall (p p':product), {p=p'}+{~p=p'}.
Proof.
  destruct p; destruct p'; try solve [done_right | auto].
    destruct (@gvar_dec g g0); subst; try solve [auto | done_right]. 
    destruct (@fdec_dec f f0); subst; try solve [auto | done_right]. 
    destruct (@fdef_dec f f0); subst; try solve [auto | done_right]. 
Qed.

Lemma products_dec : forall (lp lp':products), {lp=lp'}+{~lp=lp'}.
Proof.
  induction lp.
    destruct lp'; subst; try solve [subst; auto | done_right].

    destruct lp'; subst; try solve [done_right].
    destruct (@product_dec a p); subst; try solve [done_right].
    destruct (@IHlp lp'); subst; try solve [auto | done_right].
Qed.

Lemma namedt_dec : forall (nt1 nt2:namedt), {nt1=nt2}+{~nt1=nt2}.
Proof.
  destruct nt1; destruct nt2; try solve [subst; auto | done_right].
    destruct (@id_dec i0 i1); subst; try solve [done_right].
    destruct (@typ_dec t t0); subst; try solve [auto | done_right].
Qed.

Lemma namedts_dec : forall (nts nts':namedts), {nts=nts'}+{~nts=nts'}.
Proof.
  induction nts.
    destruct nts'; subst; try solve [subst; auto | done_right].

    destruct nts'; subst; try solve [done_right].
    destruct (@namedt_dec a n); subst; try solve [done_right].
    destruct (@IHnts nts'); subst; try solve [auto | done_right].
Qed.

Lemma layout_dec : forall (l1 l2:layout), {l1=l2}+{~l1=l2}.
Proof.
  destruct l1; destruct l2; try solve [subst; auto | done_right].
    destruct (@Size.dec s s0); subst; try solve [done_right].
    destruct (@Align.dec a a1); subst; try solve [done_right].
    destruct (@Align.dec a0 a2); subst; try solve [auto | done_right].

    destruct (@Size.dec s s0); subst; try solve [done_right].
    destruct (@Align.dec a a1); subst; try solve [done_right].
    destruct (@Align.dec a0 a2); subst; try solve [auto | done_right].

    destruct (@Size.dec s s0); subst; try solve [done_right].
    destruct (@Align.dec a a1); subst; try solve [done_right].
    destruct (@Align.dec a0 a2); subst; try solve [auto | done_right].

    destruct (@Size.dec s s0); subst; try solve [done_right].
    destruct (@Align.dec a a1); subst; try solve [done_right].
    destruct (@Align.dec a0 a2); subst; try solve [auto | done_right].

    destruct (@Size.dec s s0); subst; try solve [done_right].
    destruct (@Align.dec a a1); subst; try solve [done_right].
    destruct (@Align.dec a0 a2); subst; try solve [auto | done_right].
Qed.  

Lemma layouts_dec : forall (l1 l2:layouts), {l1=l2}+{~l1=l2}.
Proof.
  induction l1.
    destruct l2; subst; try solve [subst; auto | done_right].

    destruct l2; subst; try solve [done_right].
    destruct (@layout_dec a l0); subst; try solve [done_right].
    destruct (@IHl1 l2); subst; try solve [auto | done_right].
Qed.

Lemma module_dec : forall (m m':module), {m=m'}+{~m=m'}.
Proof.
  destruct m; destruct m'; try solve [done_right | auto].
    destruct (@layouts_dec l0 l1); subst; try solve [done_right]. 
    destruct (@namedts_dec n n0); subst; try solve [done_right]. 
    destruct (@products_dec p p0); subst; try solve [auto | done_right]. 
Qed.

Lemma modules_dec : forall (lm lm':modules), {lm=lm'}+{~lm=lm'}.
Proof.
  induction lm.
    destruct lm'; subst; try solve [subst; auto | done_right].

    destruct lm'; subst; try solve [done_right].
    destruct (@module_dec a m); subst; try solve [done_right].
    destruct (@IHlm lm'); subst; try solve [auto | done_right].
Qed.

Lemma system_dec : forall (s s':system), {s=s'}+{~s=s'}.
Proof.
  apply modules_dec.
Qed.

(**********************************)
(* Eq. *)
Definition typEqB t1 t2 := sumbool2bool _ _ (typ_dec t1 t2).

Definition list_typEqB lt1 lt2 := sumbool2bool _ _ (list_typ_dec lt1 lt2).

Definition idEqB i i' := sumbool2bool _ _ (id_dec i i').

Definition constEqB c1 c2 := sumbool2bool _ _ (const_dec c1 c2).

Definition list_constEqB lc1 lc2 := sumbool2bool _ _ (list_const_dec lc1 lc2).

Definition valueEqB (v v':value) := sumbool2bool _ _ (value_dec v v').

Definition paramsEqB (lp lp':params) := sumbool2bool _ _ (params_dec lp lp').

Definition lEqB i i' := sumbool2bool _ _ (l_dec i i').

Definition list_value_lEqB (idls idls':list_value_l) := sumbool2bool _ _ (list_value_l_dec idls idls').

Definition list_valueEqB idxs idxs' := sumbool2bool _ _ (list_value_dec idxs idxs').

Definition bopEqB (op op':bop) := sumbool2bool _ _ (bop_dec op op').
Definition extopEqB (op op':extop) := sumbool2bool _ _ (extop_dec op op').
Definition condEqB (c c':cond) := sumbool2bool _ _ (cond_dec c c').
Definition castopEqB (c c':castop) := sumbool2bool _ _ (castop_dec c c').

Definition cmdEqB (i i':cmd) := sumbool2bool _ _ (cmd_dec i i').

Definition cmdsEqB (cs1 cs2:list cmd) := sumbool2bool _ _ (cmds_dec cs1 cs2).
  
Definition terminatorEqB (i i':terminator) := sumbool2bool _ _ (terminator_dec i i').

Definition phinodeEqB (i i':phinode) := sumbool2bool _ _ (phinode_dec i i').

Definition phinodesEqB (ps1 ps2:list phinode) := sumbool2bool _ _ (phinodes_dec ps1 ps2).

Definition blockEqB (b1 b2:block) := sumbool2bool _ _ (block_dec b1 b2).

Definition blocksEqB (lb lb':blocks) := sumbool2bool _ _ (blocks_dec lb lb').

Definition argsEqB (la la':args) := sumbool2bool _ _ (args_dec la la').

Definition fheaderEqB (fh fh' : fheader) := sumbool2bool _ _ (fheader_dec fh fh').

Definition fdecEqB (fd fd' : fdec) := sumbool2bool _ _ (fdec_dec fd fd').

Definition fdefEqB (fd fd' : fdef) := sumbool2bool _ _ (fdef_dec fd fd').

Definition gvarEqB (gv gv' : gvar) := sumbool2bool _ _ (gvar_dec gv gv').

Definition productEqB (p p' : product) := sumbool2bool _ _ (product_dec p p').

Definition productsEqB (lp lp':products) := sumbool2bool _ _ (products_dec lp lp').

Definition layoutEqB (o o' : layout) := sumbool2bool _ _ (layout_dec o o').

Definition layoutsEqB (lo lo':layouts) := sumbool2bool _ _ (layouts_dec lo lo').

Definition moduleEqB (m m':module) := sumbool2bool _ _ (module_dec m m').

Definition modulesEqB (lm lm':modules) := sumbool2bool _ _ (modules_dec lm lm').

Definition systemEqB (s s':system) := sumbool2bool _ _ (system_dec s s').

Definition attributeEqB (attr attr':attribute) := 
  sumbool2bool _ _ (attribute_dec attr attr').

Definition attributesEqB (attrs attrs':attributes) := 
  sumbool2bool _ _ (attributes_dec attrs attrs').

Definition linkageEqB (lk lk':linkage) := sumbool2bool _ _ (linkage_dec lk lk').

Definition visibilityEqB (v v':visibility) := 
  sumbool2bool _ _ (visibility_dec v v').

Definition callconvEqB (cc cc':callconv) := 
  sumbool2bool _ _ (callconv_dec cc cc').

(**********************************)
(* Inclusion. *)

Fixpoint InCmdsB (i:cmd) (li:cmds) {struct li} : bool :=
match li with
| nil => false
| i' :: li' => cmdEqB i i' || InCmdsB i li'
end.

Fixpoint InPhiNodesB (i:phinode) (li:phinodes) {struct li} : bool :=
match li with
| nil => false
| i' :: li' => phinodeEqB i i' || InPhiNodesB i li'
end.

Definition cmdInBlockB (i:cmd) (b:block) : bool :=
match b with
| block_intro l _ cmds _ => InCmdsB i cmds
end.

Definition phinodeInBlockB (i:phinode) (b:block) : bool :=
match b with
| block_intro l ps _ _ => InPhiNodesB i ps
end.

Definition terminatorInBlockB (i:terminator) (b:block) : bool :=
match b with
| block_intro l _ _ t => terminatorEqB i t
end.

Fixpoint InArgsB (a:arg) (la:args) {struct la} : bool :=
match la with
| nil => false
| a' :: la' => 
  match (a, a') with
  | ((t, attrs, id), (t', attrs', id')) => 
       typEqB t t' && attributesEqB attrs attrs' && idEqB id id'
  end ||
  InArgsB a la'
end.

Definition argInFheaderB (a:arg) (fh:fheader) : bool :=
match fh with
| (fheader_intro _ t id la _) => InArgsB a la
end.

Definition argInFdecB (a:arg) (fd:fdec) : bool :=
match fd with
| (fdec_intro fh) => argInFheaderB a fh
end.

Definition argInFdefB (a:arg) (fd:fdef) : bool :=
match fd with
| (fdef_intro fh lb) => argInFheaderB a fh
end.

Fixpoint InBlocksB (b:block) (lb:blocks) {struct lb} : bool :=
match lb with
| nil => false
| b' :: lb' => blockEqB b b' || InBlocksB b lb'
end.

Definition blockInFdefB (b:block) (fd:fdef) : bool :=
match fd with
| (fdef_intro fh lb) => InBlocksB b lb
end.

Fixpoint InProductsB (p:product) (lp:products) {struct lp} : bool :=
match lp with
| nil => false
| p' :: lp' => productEqB p p' || InProductsB p lp'
end.

Definition productInModuleB (p:product) (m:module) : bool :=
let (os, nts, ps) := m in
InProductsB p ps.

Fixpoint InModulesB (m:module) (lm:modules) {struct lm} : bool :=
match lm with
| nil => false
| m' :: lm' => moduleEqB m m' || InModulesB m lm'
end.

Definition moduleInSystemB (m:module) (s:system) : bool :=
InModulesB m s.

Definition productInSystemModuleB (p:product) (s:system) (m:module) : bool :=
moduleInSystemB m s && productInModuleB p m.

Definition blockInSystemModuleFdefB (b:block) (s:system) (m:module) (f:fdef) 
  : bool :=
blockInFdefB b f && productInSystemModuleB (product_fdef f) s m.

Definition cmdInSystemModuleFdefBlockB   
  (i:cmd) (s:system) (m:module) (f:fdef) (b:block) : bool :=
cmdInBlockB i b && blockInSystemModuleFdefB b s m f.

Definition phinodeInSystemModuleFdefBlockB 
  (i:phinode) (s:system) (m:module) (f:fdef) (b:block) : bool :=
phinodeInBlockB i b && blockInSystemModuleFdefB b s m f.

Definition terminatorInSystemModuleFdefBlockB 
  (i:terminator) (s:system) (m:module) (f:fdef) (b:block) : bool :=
terminatorInBlockB i b && blockInSystemModuleFdefB b s m f.

Definition insnInSystemModuleFdefBlockB 
  (i:insn) (s:system) (m:module) (f:fdef) (b:block) : bool :=
match i with
| insn_phinode p => phinodeInSystemModuleFdefBlockB p s m f b
| insn_cmd c => cmdInSystemModuleFdefBlockB c s m f b
| insn_terminator t => terminatorInSystemModuleFdefBlockB t s m f b
end.

Definition insnInFdefBlockB 
  (i:insn) (f:fdef) (b:block) : bool :=
match i with
| insn_phinode p => phinodeInBlockB p b && blockInFdefB b f
| insn_cmd c => cmdInBlockB c b && blockInFdefB b f
| insn_terminator t => terminatorInBlockB t b && blockInFdefB b f
end.

Definition blockInSystemModuleFdef b S M F := 
  blockInSystemModuleFdefB b S M F = true.

Definition moduleInSystem M S := moduleInSystemB M S = true.

(**********************************)
(* parent *)

(* matching (cmdInBlockB i b) in getParentOfCmdFromBlocksC directly makes
   the compilation very slow, so we define this dec lemma first... *)
Lemma cmdInBlockB_dec : forall i b,
  {cmdInBlockB i b = true} + {cmdInBlockB i b = false}.
Proof.
  intros i0 b. destruct (cmdInBlockB i0 b); auto.
Qed.

Lemma phinodeInBlockB_dec : forall i b,
  {phinodeInBlockB i b = true} + {phinodeInBlockB i b = false}.
Proof.
  intros i0 b. destruct (phinodeInBlockB i0 b); auto.
Qed.

Lemma terminatorInBlockB_dec : forall i b,
  {terminatorInBlockB i b = true} + {terminatorInBlockB i b = false}.
Proof.
  intros i0 b. destruct (terminatorInBlockB i0 b); auto.
Qed.

Fixpoint getParentOfCmdFromBlocks (i:cmd) (lb:blocks) {struct lb} : option block :=
match lb with
| nil => None
| b::lb' => 
  match (cmdInBlockB_dec i b) with
  | left _ => Some b
  | right _ => getParentOfCmdFromBlocks i lb'
  end
end.

Definition getParentOfCmdFromFdef (i:cmd) (fd:fdef) : option block :=
match fd with
| (fdef_intro _ lb) => getParentOfCmdFromBlocks i lb
end.

Definition getParentOfCmdFromProduct (i:cmd) (p:product) : option block :=
match p with
| (product_fdef fd) => getParentOfCmdFromFdef i fd
| _ => None
end.

Fixpoint getParentOfCmdFromProducts (i:cmd) (lp:products) {struct lp} : option block :=
match lp with
| nil => None
| p::lp' =>
  match (getParentOfCmdFromProduct i p) with
  | Some b => Some b
  | None => getParentOfCmdFromProducts i lp'
  end
end.

Definition getParentOfCmdFromModule (i:cmd) (m:module) : option block := 
  let (os, nts, ps) := m in
  getParentOfCmdFromProducts i ps.

Fixpoint getParentOfCmdFromModules (i:cmd) (lm:modules) {struct lm} : option block :=
match lm with
| nil => None
| m::lm' =>
  match (getParentOfCmdFromModule i m) with
  | Some b => Some b
  | None => getParentOfCmdFromModules i lm'
  end
end.

Definition getParentOfCmdFromSystem (i:cmd) (s:system) : option block := 
  getParentOfCmdFromModules i s.

Definition cmdHasParent (i:cmd) (s:system) : bool :=
match (getParentOfCmdFromSystem i s) with
| Some _ => true
| None => false
end.

Fixpoint getParentOfPhiNodeFromBlocks (i:phinode) (lb:blocks) {struct lb} : option block :=
match lb with
| nil => None
| b::lb' => 
  match (phinodeInBlockB_dec i b) with
  | left _ => Some b
  | right _ => getParentOfPhiNodeFromBlocks i lb'
  end
end.

Definition getParentOfPhiNodeFromFdef (i:phinode) (fd:fdef) : option block :=
match fd with
| (fdef_intro _ lb) => getParentOfPhiNodeFromBlocks i lb
end.

Definition getParentOfPhiNodeFromProduct (i:phinode) (p:product) : option block :=
match p with
| (product_fdef fd) => getParentOfPhiNodeFromFdef i fd
| _ => None
end.

Fixpoint getParentOfPhiNodeFromProducts (i:phinode) (lp:products) {struct lp} : option block :=
match lp with
| nil => None
| p::lp' =>
  match (getParentOfPhiNodeFromProduct i p) with
  | Some b => Some b
  | None => getParentOfPhiNodeFromProducts i lp'
  end
end.

Definition getParentOfPhiNodeFromModule (i:phinode) (m:module) : option block := 
  let (os, nts, ps) := m in
  getParentOfPhiNodeFromProducts i ps.

Fixpoint getParentOfPhiNodeFromModules (i:phinode) (lm:modules) {struct lm} : option block :=
match lm with
| nil => None
| m::lm' =>
  match (getParentOfPhiNodeFromModule i m) with
  | Some b => Some b
  | None => getParentOfPhiNodeFromModules i lm'
  end
end.

Definition getParentOfPhiNodeFromSystem (i:phinode) (s:system) : option block := 
  getParentOfPhiNodeFromModules i s.

Definition phinodeHasParent (i:phinode) (s:system) : bool :=
match (getParentOfPhiNodeFromSystem i s) with
| Some _ => true
| None => false
end.

Fixpoint getParentOfTerminatorFromBlocks (i:terminator) (lb:blocks) {struct lb} : option block :=
match lb with
| nil => None
| b::lb' => 
  match (terminatorInBlockB_dec i b) with
  | left _ => Some b
  | right _ => getParentOfTerminatorFromBlocks i lb'
  end
end.

Definition getParentOfTerminatorFromFdef (i:terminator) (fd:fdef) : option block :=
match fd with
| (fdef_intro _ lb) => getParentOfTerminatorFromBlocks i lb
end.

Definition getParentOfTerminatorFromProduct (i:terminator) (p:product) : option block :=
match p with
| (product_fdef fd) => getParentOfTerminatorFromFdef i fd
| _ => None
end.

Fixpoint getParentOfTerminatorFromProducts (i:terminator) (lp:products) {struct lp} : option block :=
match lp with
| nil => None
| p::lp' =>
  match (getParentOfTerminatorFromProduct i p) with
  | Some b => Some b
  | None => getParentOfTerminatorFromProducts i lp'
  end
end.

Definition getParentOfTerminatorFromModule (i:terminator) (m:module) : option block := 
  let (os, nts, ps) := m in
  getParentOfTerminatorFromProducts i ps.

Fixpoint getParentOfTerminatorFromModules (i:terminator) (lm:modules) {struct lm} : option block :=
match lm with
| nil => None
| m::lm' =>
  match (getParentOfTerminatorFromModule i m) with
  | Some b => Some b
  | None => getParentOfTerminatorFromModules i lm'
  end
end.

Definition getParentOfTerminatorFromSystem (i:terminator) (s:system) : option block := 
  getParentOfTerminatorFromModules i s.

Definition terminatoreHasParent (i:terminator) (s:system) : bool :=
match (getParentOfTerminatorFromSystem i s) with
| Some _ => true
| None => false
end.

Lemma productInModuleB_dec : forall b m,
  {productInModuleB b m = true} + {productInModuleB b m = false}.
Proof.
  intros b m. destruct (productInModuleB b m); auto.
Qed.

Fixpoint getParentOfFdefFromModules (fd:fdef) (lm:modules) {struct lm} : option module :=
match lm with
| nil => None
| m::lm' => 
  match (productInModuleB_dec (product_fdef fd) m) with
  | left _ => Some m
  | right _ => getParentOfFdefFromModules fd lm'
  end
end.

Definition getParentOfFdefFromSystem (fd:fdef) (s:system) : option module := 
  getParentOfFdefFromModules fd s.

Notation "t =t= t' " := (typEqB t t') (at level 50).
Notation "n =n= n'" := (beq_nat n n') (at level 50).
Notation "b =b= b'" := (blockEqB b b') (at level 50).
Notation "i =cmd= i'" := (cmdEqB i i') (at level 50).
Notation "i =phi= i'" := (phinodeEqB i i') (at level 50).
Notation "i =tmn= i'" := (terminatorEqB i i') (at level 50).

(**********************************)
(* Check to make sure that if there is more than one entry for a
   particular basic block in this PHI node, that the incoming values 
   are all identical. *)
Fixpoint lookupIdsViaLabelFromIdls (idls:list_value_l) (l0:l) : list id :=
match idls with
| Nil_list_value_l => nil
| Cons_list_value_l (value_id id1) l1 idls' =>
  if (eq_dec l0 l1) 
  then set_add eq_dec id1 (lookupIdsViaLabelFromIdls idls' l0)
  else (lookupIdsViaLabelFromIdls idls' l0)
| Cons_list_value_l _ l1 idls' =>
  lookupIdsViaLabelFromIdls idls' l0
end.

Fixpoint _checkIdenticalIncomingValues (idls idls0:list_value_l) : Prop :=
match idls with
| Nil_list_value_l => True
| Cons_list_value_l _ l idls' => 
  (length (lookupIdsViaLabelFromIdls idls0 l) <= 1)%nat /\
  (_checkIdenticalIncomingValues idls' idls0)
end.

Definition checkIdenticalIncomingValues (PN:phinode) : Prop :=
match PN with
| insn_phi _ _ idls => _checkIdenticalIncomingValues idls idls
end.

(**********************************)
(* Instruction Signature *)

Module Type SigValue.

 Parameter getNumOperands : insn -> nat.

End SigValue.

Module Type SigUser. 
 Include SigValue.

End SigUser.

Module Type SigConstant.
 Include SigValue.

 Parameter getTyp : const -> option typ.

End SigConstant.

Module Type SigGlobalValue.
 Include SigConstant.

End SigGlobalValue.

Module Type SigFunction.
 Include SigGlobalValue.

 Parameter getDefReturnType : fdef -> typ.
 Parameter getDefFunctionType : fdef -> typ.
 Parameter def_arg_size : fdef -> nat.
 
 Parameter getDecReturnType : fdec -> typ.
 Parameter getDecFunctionType : fdec -> typ.
 Parameter dec_arg_size : fdec -> nat.

End SigFunction.

Module Type SigInstruction.
 Include SigUser.

(* Parameter isInvokeInst : insn -> bool. *)
 Parameter isCallInst : cmd -> bool.

End SigInstruction.

Module Type SigReturnInst.
 Include SigInstruction.

 Parameter hasReturnType : terminator -> bool.
 Parameter getReturnType : terminator -> option typ.

End SigReturnInst.

Module Type SigCallSite.
(* Parameter getCalledFunction : cmd -> system -> option fdef. *)
 Parameter getFdefTyp : fdef -> typ.
 Parameter arg_size : fdef -> nat.
 Parameter getArgument : fdef -> nat -> option arg.
 Parameter getArgumentType : fdef -> nat -> option typ.

End SigCallSite.

Module Type SigCallInst.
 Include SigInstruction.

End SigCallInst.

(*
Module Type SigInvokeInst.
 Include SigInstruction.

 Parameter getNormalDest : system -> insn -> option block.

End SigInvokeInst.
*)

Module Type SigBinaryOperator.
 Include SigInstruction.

 Parameter getFirstOperandType : fdef -> cmd -> option typ.
 Parameter getSecondOperandType : fdef -> cmd -> option typ.
 Parameter getResultType : cmd -> option typ.

End SigBinaryOperator.

Module Type SigPHINode.
 Include SigInstruction.

 Parameter getNumIncomingValues : phinode -> nat.
 Parameter getIncomingValueType : fdef  -> phinode -> i -> option typ.
End SigPHINode.

(* Type Signature *)

Module Type SigType.
 Parameter isIntOrIntVector : typ -> bool.
 Parameter isInteger : typ -> bool.
 Parameter isSized : typ -> bool.
 Parameter getPrimitiveSizeInBits : typ -> sz.
End SigType.

Module Type SigDerivedType.
 Include SigType.
End SigDerivedType.

Module Type SigFunctionType.
 Include SigDerivedType.

 Parameter getNumParams : typ -> option nat.
 Parameter isVarArg : typ -> bool.
 Parameter getParamType : typ -> nat -> option typ.
End SigFunctionType.

Module Type SigCompositeType.
 Include SigDerivedType.
End SigCompositeType.

Module Type SigSequentialType.
 Include SigCompositeType.

 Parameter hasElementType : typ -> bool.
 Parameter getElementType : typ -> option typ.

End SigSequentialType.

Module Type SigArrayType.
 Include SigSequentialType.

 Parameter getNumElements : typ -> nat.

End SigArrayType.

(* Instruction Instantiation *)

Module Value <: SigValue.

 Definition getNumOperands (i:insn) : nat := 
   length (getInsnOperands i).  

End Value.

Module User <: SigUser. Include Value.

End User.

Module Constant <: SigConstant.
 Include Value.

Fixpoint wf_zeroconst_typ (t:typ) : Prop :=
match t with
| typ_int sz => True
| typ_floatpoint fp =>
  match fp with
  | fp_float | fp_double => True
  | _ => False (* FIXME: not supported 80 and 128 yet. *)
  end
| typ_void | typ_label | typ_metadata => False
| typ_array sz t => wf_zeroconst_typ t
| typ_struct ts => wf_zeroconsts_typ ts
| typ_pointer t' => True
| typ_function _ _ _ => False
| typ_opaque => False
| typ_namedt _ => False
end             
with wf_zeroconsts_typ (lt:list_typ) : Prop := 
match lt with
| Nil_list_typ => True
| Cons_list_typ t lt' => wf_zeroconsts_typ lt' /\ wf_zeroconst_typ t
end
.

Definition wf_zeroconst TD t := wf_zeroconst_typ t /\ LLVMtd.feasible_typ TD t.

Fixpoint getTyp (c:const) : option typ :=
 match c with
 | const_zeroinitializer t => Some t
 | const_int sz _ => Some (typ_int sz)
 | const_floatpoint fp _ => Some (typ_floatpoint fp)
 | const_undef t => Some t
 | const_null t => Some (typ_pointer t)
 | const_arr t lc => 
   Some
   (match lc with
   | Nil_list_const => typ_array Size.Zero t
   | Cons_list_const c' lc' => typ_array (Size.from_nat (length (unmake_list_const lc))) t
   end)
 | const_struct lc => 
   match getList_typ lc with
   | Some lt => Some (typ_struct lt)
   | None => None
   end
 | const_gid t _ => Some (typ_pointer t)
 | const_truncop _ _ t => Some t
 | const_extop _ _ t => Some t
 | const_castop _ _ t => Some t
 | const_gep _ c idxs => 
   match (getTyp c) with
   | Some t => getConstGEPTyp idxs t
   | _ => None
   end
 | const_select c0 c1 c2 => getTyp c1
 | const_icmp c c1 c2 => Some (typ_int Size.One)
 | const_fcmp fc c1 c2 => Some (typ_int Size.One)
 | const_extractvalue c idxs =>
   match (getTyp c) with
   | Some t => getSubTypFromConstIdxs idxs t
   | _ => None
   end
 | const_insertvalue c c' lc => getTyp c'
 | const_bop _ c1 c2 => getTyp c1
 | const_fbop _ c1 c2 => getTyp c1
 end
with getList_typ (cs:list_const) : option list_typ :=
match cs with
| Nil_list_const => Some Nil_list_typ
| Cons_list_const c cs' => 
  match (getTyp c, getList_typ cs') with
  | (Some t, Some ts') => Some (Cons_list_typ t ts')
  | (_, _) => None
  end
end.


Fixpoint gen_utyp_maps_aux (cid:id) (m:list(id*typ)) (t:typ) : option typ :=
 match t with
 | typ_int s => Some (typ_int s)
 | typ_floatpoint f => Some (typ_floatpoint f)
 | typ_void => Some typ_void
 | typ_label => Some typ_label
 | typ_metadata => Some typ_metadata
 | typ_array s t0 => do ut0 <- gen_utyp_maps_aux cid m t0; ret (typ_array s ut0)
 | typ_function t0 ts0 va => 
     do ut0 <- gen_utyp_maps_aux cid m t0;
     do uts0 <- gen_utyps_maps_aux cid m ts0;
        ret (typ_function ut0 uts0 va)
 | typ_struct ts0 => 
     do uts0 <- gen_utyps_maps_aux cid m ts0; ret (typ_struct uts0)
 | typ_pointer t0 => 
     match gen_utyp_maps_aux cid m t0 with
     | Some ut0 => Some (typ_pointer ut0)
     | None => 
         match t0 with
         | typ_namedt i => if eq_atom_dec i cid then Some t else None
         | _ => None
         end
     end
 | typ_opaque => Some typ_opaque
 | typ_namedt i => lookupAL _ m i
 end
with gen_utyps_maps_aux (cid:id) (m:list(id*typ)) (ts:list_typ) : option list_typ
   := 
 match ts with
 | Nil_list_typ => Some Nil_list_typ
 | Cons_list_typ t0 ts0 =>
     do ut0 <- gen_utyp_maps_aux cid m t0; 
     do uts0 <- gen_utyps_maps_aux cid m ts0; 
     ret (Cons_list_typ ut0 uts0)
 end.

Fixpoint gen_utyp_maps (nts:namedts) : list (id*typ) :=
match nts with
| nil => nil 
| namedt_intro id0 t::nts' =>
  let results := gen_utyp_maps nts' in
  match gen_utyp_maps_aux id0 results t with
  | None => results
  | Some r => (id0, r)::results
  end
end.

Fixpoint typ2utyp_aux (m:list(id*typ)) (t:typ) : option typ :=
 match t with
 | typ_int s => Some (typ_int s)
 | typ_floatpoint f => Some (typ_floatpoint f)
 | typ_void => Some typ_void
 | typ_label => Some typ_label
 | typ_metadata => Some typ_metadata
 | typ_array s t0 => do ut0 <- typ2utyp_aux m t0; ret (typ_array s ut0)
 | typ_function t0 ts0 va => 
     do ut0 <- typ2utyp_aux m t0;
     do uts0 <- typs2utyps_aux m ts0;
        ret (typ_function ut0 uts0 va)
 | typ_struct ts0 => do uts0 <- typs2utyps_aux m ts0; ret (typ_struct uts0)
 | typ_pointer t0 => do ut0 <- typ2utyp_aux m t0; ret (typ_pointer ut0)
 | typ_opaque => Some typ_opaque
 | typ_namedt i => lookupAL _ m i
 end
with typs2utyps_aux (m:list(id*typ)) (ts:list_typ) : option list_typ := 
 match ts with
 | Nil_list_typ => Some Nil_list_typ
 | Cons_list_typ t0 ts0 =>
     do ut0 <- typ2utyp_aux m t0; 
     do uts0 <- typs2utyps_aux m ts0; 
     ret (Cons_list_typ ut0 uts0)
 end.

Definition typ2utyp' (nts:namedts) (t:typ) : option typ :=
let m := gen_utyp_maps (List.rev nts) in
typ2utyp_aux m t.

Fixpoint subst_typ (i':id) (t' t:typ) : typ :=
 match t with
 | typ_int _ | typ_floatpoint _ | typ_void | typ_label | typ_metadata 
 | typ_opaque => t
 | typ_array s t0 => typ_array s (subst_typ i' t' t0)
 | typ_function t0 ts0 va => 
     typ_function (subst_typ i' t' t0) (subst_typs i' t' ts0) va
 | typ_struct ts0 => typ_struct (subst_typs i' t' ts0)
 | typ_pointer t0 => typ_pointer (subst_typ i' t' t0)
 | typ_namedt i => if (eq_atom_dec i i') then t' else t
 end
with subst_typs (i':id) (t':typ) (ts:list_typ) : list_typ := 
 match ts with
 | Nil_list_typ => Nil_list_typ
 | Cons_list_typ t0 ts0 =>
     Cons_list_typ (subst_typ i' t' t0) (subst_typs i' t' ts0)
 end.

Fixpoint subst_typ_by_nts (nts:namedts) (t:typ) : typ :=
match nts with
| nil => t
| (namedt_intro id' t')::nts' => subst_typ_by_nts nts' (subst_typ id' t' t)
end.

Fixpoint subst_nts_by_nts (nts0 nts:namedts) : list (id*typ) :=
match nts with
| nil => nil
| (namedt_intro id' t')::nts' => 
    (id',(subst_typ_by_nts nts0 t'))::subst_nts_by_nts nts0 nts'
end.

Definition typ2utyp (nts:namedts) (t:typ) : option typ :=
let m := subst_nts_by_nts nts nts in
typ2utyp_aux m t.

Definition unifiable_typ (TD:LLVMtd.TargetData) (t:typ) : Prop :=
  let '(los,nts) := TD in
  exists ut, typ2utyp nts t = Some ut /\ 
    LLVMtd.getTypeAllocSize TD ut = LLVMtd.getTypeAllocSize TD t.

End Constant.

Module GlobalValue <: SigGlobalValue.
 Include Constant.

End GlobalValue.

Module Function <: SigFunction.
 Include GlobalValue.

 Definition getDefReturnType (fd:fdef) : typ :=
 match fd with
 | fdef_intro (fheader_intro _ t _ _ _ ) _ => t
 end.

 Definition getDefFunctionType (fd:fdef) : typ := getFdefTyp fd.

 Definition def_arg_size (fd:fdef) : nat :=
 match fd with
 | (fdef_intro (fheader_intro _ _ _ la _) _) => length la
 end.

 Definition getDecReturnType (fd:fdec) : typ :=
 match fd with
 | fdec_intro (fheader_intro _ t _ _ _ ) => t
 end.

 Definition getDecFunctionType (fd:fdec) : typ := getFdecTyp fd.

 Definition dec_arg_size (fd:fdec) : nat :=
 match fd with
 | (fdec_intro (fheader_intro _ _ _ la _)) => length la
 end.

End Function.

Module Instruction <: SigInstruction.
 Include User.

(* Definition isInvokeInst (i:insn) : bool := isInvokeInsnB i. *)
 Definition isCallInst (i:cmd) : bool := _isCallInsnB i.

End Instruction.

Module ReturnInst <: SigReturnInst.
 Include Instruction.

 Definition hasReturnType (i:terminator) : bool :=
 match i with
 | insn_return _ t v => true
 | _ => false
 end.

 Definition getReturnType (i:terminator) : option typ :=
 match i with
 | insn_return _ t v => Some t
 | _ => None
 end.

End ReturnInst.

Module CallSite <: SigCallSite.

(*
Definition getCalledFunction (i:cmd) (s:system) : option fdef :=
 match i with 
 (* | insn_invoke _ _ fid _ _ _ => lookupFdefViaIDFromSystemC s fid *)
 | insn_call _ _ _ _ fid _ => lookupFdefViaIDFromSystem s fid
 | _ => None
 end.
*)

 Definition getFdefTyp (fd:fdef) : typ := getFdefTyp fd.

 Definition arg_size (fd:fdef) : nat :=
 match fd with
 | (fdef_intro (fheader_intro _ _ _ la _) _) => length la
 end.

 Definition getArgument (fd:fdef) (i:nat) : option arg :=
 match fd with
 | (fdef_intro (fheader_intro _ _ _ la _) _) =>
    match (nth_error la i) with
    | Some a => Some a
    | None => None
    end
 end. 

 Definition getArgumentType (fd:fdef) (i:nat) : option typ :=
 match (getArgument fd i) with
 | Some (t, _, _) => Some t
 | None => None
 end.

End CallSite.

Module CallInst <: SigCallInst.
 Include Instruction.

End CallInst.

(*
Module InvokeInst <: SigInvokeInst.
 Include Instruction.

 Definition getNormalDest (s:system) (i:insn) : option block :=
 match (getNormalDestFromInvokeInsnC i) with
 | None => None
 | Some l => lookupBlockViaLabelFromSystem s l
 end.

End InvokeInst.
*)

Module BinaryOperator <: SigBinaryOperator.
 Include Instruction.

 Definition getFirstOperandType (f:fdef) (i:cmd) : option typ := 
 match i with
 | insn_bop _ _ _ v1 _ => 
   match v1 with
   | value_id id1 => lookupTypViaIDFromFdef f id1
   | value_const c => Constant.getTyp c
   end
 | _ => None
 end.

 Definition getSecondOperandType (f:fdef) (i:cmd) : option typ := 
 match i with
 | insn_bop _ _ _ _ v2 => 
   match v2 with
   | value_id id2 => lookupTypViaIDFromFdef f id2
   | value_const c => Constant.getTyp c
   end
 | _ => None
 end.

 Definition getResultType (i:cmd) : option typ := getCmdTyp i.

End BinaryOperator.

Module PHINode <: SigPHINode.
 Include Instruction.

 Definition getNumIncomingValues (i:phinode) : nat :=
 match i with
 | (insn_phi _ _ ln) => (length (unmake_list_value_l ln))
 end.

 Definition getIncomingValueType (f:fdef) (i:phinode) (n:nat) : option typ :=
 match i with
 | (insn_phi _ _ ln) => 
    match (nth_list_value_l n ln) with
    | Some (value_id id, _) => lookupTypViaIDFromFdef f id
    | Some (value_const c, _) => Constant.getTyp c
    | None => None
    end
 end.

End PHINode.

(* Type Instantiation *)

Module Typ <: SigType.
 Definition isIntOrIntVector (t:typ) : bool :=
 match t with
 | typ_int _ => true
 | _ => false
 end.

 Definition isInteger (t:typ) : bool :=
 match t with
 | typ_int _ => true
 | _ => false
 end.

 (* isSizedDerivedType - Derived types like structures and arrays are sized
    iff all of the members of the type are sized as well.  Since asking for
    their size is relatively uncommon, move this operation out of line. 

    isSized - Return true if it makes sense to take the size of this type.  To
    get the actual size for a particular target, it is reasonable to use the
    TargetData subsystem to do this. *)
 Fixpoint isSized (t:typ) : bool :=
 match t with
 | typ_int _ => true
 | typ_floatpoint _ => true
 | typ_array _ t' => isSized t'
 | typ_struct lt => isSizedListTyp lt
 | typ_pointer _ => true
 | _ => false
 end
 with isSizedListTyp (lt : list_typ) : bool :=
 match lt with
 | Nil_list_typ => true
 | Cons_list_typ t lt' => isSized t && isSizedListTyp lt'
 end. 

  Definition getPrimitiveSizeInBits (t:typ) : sz :=
  match t with
  | typ_int sz => sz
  | _ => Size.Zero
  end.

End Typ.

Module DerivedType <: SigDerivedType.
 Include Typ.
End DerivedType.

Module FunctionType <: SigFunctionType.
 Include DerivedType.

 Definition getNumParams (t:typ) : option nat :=
 match t with
 | (typ_function _ lt _) => 
     Some (length (unmake_list_typ lt))
 | _ => None
 end.

 Definition isVarArg (t:typ) : bool := false.

 Definition getParamType (t:typ) (i:nat) : option typ :=
 match t with
 | (typ_function _ lt _) => 
    match (nth_list_typ i lt) with
    | Some t => Some t
    | None => None
    end
 | _ => None
 end.

End FunctionType.

Module CompositeType <: SigCompositeType.
 Include DerivedType.
End CompositeType.

Module SequentialType <: SigSequentialType.
 Include CompositeType.

 Definition hasElementType (t:typ) : bool :=
 match t with
 | typ_array _ t' => true
 | _ => false
 end.

 Definition getElementType (t:typ) : option typ :=
 match t with
 | typ_array _ t' => Some t'
 | _ => None
 end.

End SequentialType.

Module ArrayType <: SigArrayType.
 Include SequentialType.

 Definition getNumElements (t:typ) : nat :=
 match t with
 | typ_array N _ => Size.to_nat N
 | _ => 0%nat
 end.

End ArrayType.

Definition typ2memory_chunk (t:typ) : option AST.memory_chunk :=
  match t with
  | typ_int bsz => Some (AST.Mint (Size.to_nat bsz -1))
  | typ_floatpoint fp_float => Some AST.Mfloat32
  | typ_floatpoint fp_double => Some AST.Mfloat64
  | typ_floatpoint _ => None
  | typ_pointer _ => Some (AST.Mint 31)
  | _ => None
  end.

Definition wf_alignment (TD:LLVMtd.TargetData) (t:typ) : Prop := 
forall s a (abi_or_pref:bool), 
  LLVMtd.getTypeSizeInBits_and_Alignment TD abi_or_pref t = Some (s,a) -> 
  (a > 0)%nat.

(**********************************)
(* reflect *)

Coercion is_true (b:bool) := b = true.

Inductive reflect (P:Prop) : bool -> Set :=
| ReflectT : P -> reflect P true
| ReflectF : ~P -> reflect P false
.

End LLVMinfra.


(*ENDCOPY*)

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3" "-I" "~/SVN/sol/vol/src/TV") ***
*** End: ***
 *)
