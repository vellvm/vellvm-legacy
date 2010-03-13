Require Import ssa_def.

(*BEGINCOPY*)

Require Import List.
Require Import ListSet.
Require Import Bool.
Require Import Arith.
Require Import Compare_dec.

Section SSA.

  Definition l2block := l -> option block.

  Definition mergel2block (lb1:l2block) (lb2:l2block) : l2block :=
  fun l0 =>
  match (lb1 l0, lb2 l0) with
  | (Some b1, _) => Some b1
  | (_, Some b2) => Some b2
  | (_, _) => None 
  end.

  Definition genBlock2Label_block (b:block) (f:fdef) (m:module) : l2block :=
  match b with
  | block_def l _ => fun l' => 
    match lt_eq_lt_dec l' l with 
    | inleft (right _) => Some b
    | _ => None
    end 
  end.  

  Fixpoint genBlock2Label_blocks (bs:list_block) (f:fdef) (m:module) : l2block :=
  match bs with 
  | nil => fun _ => None
  | b::bs' => mergel2block (genBlock2Label_blocks bs' f m) (genBlock2Label_block b f m)
  end.

  Definition genBlock2Label_fdef (f:fdef) (m:module) : l2block := 
  match f with
  | fdef_intro fheader blocks => genBlock2Label_blocks blocks f m 
  end.

  Fixpoint genBlock2Label (m: module) : l2block :=
  match m with 
  | module_nil => fun _ => None
  | module_global_var m' g => genBlock2Label m'
  | module_function_def m' f => mergel2block (genBlock2Label m') (genBlock2Label_fdef f m)
  | module_function_dec m' f => genBlock2Label m'
  | module_namedtype m' nt => genBlock2Label m'
  end.

End SSA.

Section UseDef.

  Definition mergeInsnUseDef (udi1:usedef_insn) (udi2:usedef_insn) : usedef_insn :=
  fun i => (udi1 i) ++ (udi2 i).

  Definition mergeBlockUseDef (udb1:usedef_block) (udb2:usedef_block) : usedef_block :=
  fun b => (udb1 b) ++ (udb2 b).

  Infix "+++" := mergeInsnUseDef (right associativity, at level 60).
  Infix "++++" := mergeBlockUseDef (right associativity, at level 60).

  Definition getInsnID (i:insn) : option id :=
  match i with
  | insn_return t v => None
  | insn_return_void  => None
  | insn_br v l1 l2 => None
  | insn_br_uncond l => None
  | insn_switch v l _ => None
  | insn_invoke id id0 paraml l1 l2 => Some id
  | insn_unreachable => None
  | insn_add id typ v1 v2 => Some id
  | insn_fadd id typ v1 v2 => Some id
  | insn_udiv id typ v1 v2 => Some id
  | insn_fdiv id typ v1 v2 => Some id
  | insn_or id typ v1 v2 => Some id
  | insn_and id typ v1 v2 =>Some id
  | insn_extractelement id N0 typ0 id0 const => Some id
  | insn_insertelement id N0 typ0 id0 typ1 v1 const2 => Some id
  | insn_extractvalue id typs id0 const1 => Some id
  | insn_insertvalue id typs id0 typ1 v1 const2 => Some id
  | insn_alloca id typ N => None
  | insn_load id typ1 id1 => Some id
  | insn_store typ1 v1 typ2 id2 => None
  | insn_trunc id typ1 v1 typ2 => Some id
  | insn_fptrunc id typ1 v1 typ2 =>Some id
  | insn_fptoui id typ1 v1 typ2 => Some id
  | insn_fptosi id typ1 v1 typ2 =>Some id
  | insn_uitofp id typ1 v1 typ2 =>Some id
  | insn_sitofp id typ1 v1 typ2 =>Some id
  | insn_ptrtoint id typ1 v1 typ2 => Some id
  | insn_inttoptr id typ1 v1 typ2 => Some id
  | insn_bitcast id typ1 v1 typ2 => Some id
  | insn_icmp id cond typ v1 v2 => Some id
  | insn_fcmp id cond typ v1 v2 => Some id
  | insn_phi id typ idls => None
  end.
 
  Definition getValueID (v:value) : option id :=
  match v with
  | value_id id => Some id
  | value_constant _ => None
  end.

  (* generate insn use-def *)

  Definition genInsnUseDef_value (v:value) (i:insn) (b:block) (f:fdef) (m:module) : usedef_insn :=
  fun i' => 
  match (getInsnID i', getValueID v) with
  | (Some id', Some id) => 
    match lt_eq_lt_dec id' id with 
    | inleft (right _) => (i, b)::nil
    | _ => nil
    end 
  |( _, _) => nil
  end.     

  Definition genInsnUseDef_id (id0:id) (i:insn) (b:block) (f:fdef) (m:module) : usedef_insn :=
  fun i' => 
  match (getInsnID i') with
  | Some id' => 
    match lt_eq_lt_dec id' id0 with 
    | inleft (right _) => (i, b)::nil
    | _ => nil
    end 
  | _ => nil
  end.     

  Fixpoint genInsnUseDef_params (ps:list_param) (i:insn) (b:block) (f:fdef) (m:module) : usedef_insn :=
  match ps with
  | nil => fun _ => nil
  | (_, v)::ps' => (genInsnUseDef_value v i b f m)+++(genInsnUseDef_params ps' i b f m)
  end.

  Definition genInsnUseDef_insn (i:insn) (b:block) (f:fdef) (m:module) : usedef_insn :=
  match i with
  | insn_return t v => genInsnUseDef_value v i b f m
  | insn_return_void  => fun _ => nil 
  | insn_br v l1 l2 => genInsnUseDef_value v i b f m        
  | insn_br_uncond l => fun _ => nil
  | insn_switch v l _ => genInsnUseDef_value v i b f m
  | insn_invoke id id0 paraml l1 l2 => (genInsnUseDef_id id0 i b f m)+++(genInsnUseDef_params paraml i b f m)
  | insn_unreachable => fun _ => nil
  | insn_add id typ v1 v2 => (genInsnUseDef_value v1 i b f m)+++(genInsnUseDef_value v2 i b f m) 
  | insn_fadd id typ v1 v2 => (genInsnUseDef_value v1 i b f m)+++(genInsnUseDef_value v2 i b f m) 	
  | insn_udiv id typ v1 v2 => (genInsnUseDef_value v1 i b f m)+++(genInsnUseDef_value v2 i b f m) 
  | insn_fdiv id typ v1 v2 => (genInsnUseDef_value v1 i b f m)+++(genInsnUseDef_value v2 i b f m) 
  | insn_or id typ v1 v2 => (genInsnUseDef_value v1 i b f m)+++(genInsnUseDef_value v2 i b f m) 
  | insn_and id typ v1 v2 => (genInsnUseDef_value v1 i b f m)+++(genInsnUseDef_value v2 i b f m) 
  | insn_extractelement id N0 typ0 id0 const => genInsnUseDef_id id0 i b f m
  | insn_insertelement id N0 typ0 id0 typ1 v1 const2 => (genInsnUseDef_id id0 i b f m)+++(genInsnUseDef_value v1 i b f m)	
  | insn_extractvalue id typs id0 const1 => genInsnUseDef_id id0 i b f m
  | insn_insertvalue id typs id0 typ1 v1 const2 => (genInsnUseDef_id id0 i b f m)+++(genInsnUseDef_value v1 i b f m)	 
  | insn_alloca id typ N => fun _ => nil
  | insn_load id typ1 id1 => genInsnUseDef_id id1 i b f m
  | insn_store typ1 v1 typ2 id2 => (genInsnUseDef_value v1 i b f m)+++(genInsnUseDef_id id2 i b f m)	 
  | insn_trunc id typ1 v1 typ2 => (genInsnUseDef_value v1 i b f m)			
  | insn_fptrunc id typ1 v1 typ2 => (genInsnUseDef_value v1 i b f m)			
  | insn_fptoui id typ1 v1 typ2 => (genInsnUseDef_value v1 i b f m)			
  | insn_fptosi id typ1 v1 typ2 => (genInsnUseDef_value v1 i b f m)			
  | insn_uitofp id typ1 v1 typ2 => (genInsnUseDef_value v1 i b f m)			
  | insn_sitofp id typ1 v1 typ2 => (genInsnUseDef_value v1 i b f m)			
  | insn_ptrtoint id typ1 v1 typ2 => (genInsnUseDef_value v1 i b f m)			
  | insn_inttoptr id typ1 v1 typ2 => (genInsnUseDef_value v1 i b f m)			
  | insn_bitcast id typ1 v1 typ2 => (genInsnUseDef_value v1 i b f m)			
  | insn_icmp id cond typ v1 v2 => (genInsnUseDef_value v1 i b f m)+++(genInsnUseDef_value v2 i b f m) 
  | insn_fcmp id cond typ v1 v2 => (genInsnUseDef_value v1 i b f m)+++(genInsnUseDef_value v2 i b f m) 
  | insn_phi id typ idls => fun _ => nil
  end.
 
  Fixpoint genInsnUseDef_insns (is:list_insn) (b:block) (f:fdef) (m:module) : usedef_insn :=
  match is with
  | nil => fun _ => nil
  | i::is' => (genInsnUseDef_insn i b f m)+++(genInsnUseDef_insns is' b f m)
  end.  

  Definition genInsnUseDef_block (b:block) (f:fdef) (m:module) : usedef_insn :=
  match b with
  | block_def l is => genInsnUseDef_insns is b f m
  end.  

  Fixpoint genInsnUseDef_blocks (bs:list_block) (f:fdef) (m:module) : usedef_insn :=
  match bs with 
  | nil => fun _ => nil
  | b::bs' => (genInsnUseDef_blocks bs' f m)+++(genInsnUseDef_block b f m)
  end.

  Definition genInsnUseDef_fdef (f:fdef) (m:module) : usedef_insn := 
  match f with
  | fdef_intro fheader blocks => genInsnUseDef_blocks blocks f m 
  end.

  Fixpoint genInsnUseDef (m: module) : usedef_insn :=
  match m with 
  | module_nil => fun _ => nil
  | module_global_var m' g => genInsnUseDef m'
  | module_function_def m' f => (genInsnUseDef m') +++ (genInsnUseDef_fdef f m)
  | module_function_dec m' f => genInsnUseDef m'
  | module_namedtype m' nt => genInsnUseDef m'
  end.

  (* generate block use-def *)

  Definition getBlockLabel (b:block) : l :=
  match b with
  | block_def l b => l
  end.

  Definition genBlockUseDef_label (l0:l) (i:insn) (b:block) (f:fdef) (m:module) : usedef_block :=
  fun b' => 
  match lt_eq_lt_dec (getBlockLabel b') l0 with 
  | inleft (right _) => (i, b)::nil
  | _ => nil
  end.

  Fixpoint genBlockUseDef_switch_cases (cs:list (const * l)) (i:insn) (b:block) (f:fdef) (m:module) : usedef_block :=
  match cs with
  | nil => fun _ => nil
  | (_, l0)::cs' => (genBlockUseDef_label l0 i b f m)++++(genBlockUseDef_switch_cases cs' i b f m)
  end.

  Fixpoint genBlockUseDef_phi_cases (ps:list (id * l)) (i:insn) (b:block) (f:fdef) (m:module) : usedef_block :=
  match ps with
  | nil => fun _ => nil
  | (_, l0)::ps' => (genBlockUseDef_label l0 i b f m)++++(genBlockUseDef_phi_cases ps' i b f m)
  end.

  Definition genBlockUseDef_insn (i:insn) (b:block) (f:fdef) (m:module) : usedef_block :=
  match i with
  | insn_return t v => fun _ => nil
  | insn_return_void  => fun _ => nil 
  | insn_br v l1 l2 => genBlockUseDef_label l1 i b f m ++++ genBlockUseDef_label l2 i b f m       
  | insn_br_uncond l => genBlockUseDef_label l i b f m
  | insn_switch v l ls => genBlockUseDef_label l i b f m ++++ genBlockUseDef_switch_cases ls i b f m
  | insn_invoke id id0 paraml l1 l2 => (genBlockUseDef_label l1 i b f m)++++(genBlockUseDef_label l2 i b f m)
  | insn_unreachable => fun _ => nil
  | insn_add id typ v1 v2 => fun _ => nil
  | insn_fadd id typ v1 v2 => fun _ => nil
  | insn_udiv id typ v1 v2 => fun _ => nil
  | insn_fdiv id typ v1 v2 => fun _ => nil
  | insn_or id typ v1 v2 => fun _ => nil
  | insn_and id typ v1 v2 => fun _ => nil
  | insn_extractelement id N0 typ0 id0 const => fun _ => nil
  | insn_insertelement id N0 typ0 id0 typ1 v1 const2 => fun _ => nil
  | insn_extractvalue id typs id0 const1 => fun _ => nil
  | insn_insertvalue id typs id0 typ1 v1 const2 => fun _ => nil
  | insn_alloca id typ N => fun _ => nil
  | insn_load id typ1 id1 => fun _ => nil
  | insn_store typ1 v1 typ2 id2 => fun _ => nil
  | insn_trunc id typ1 v1 typ2 => fun _ => nil
  | insn_fptrunc id typ1 v1 typ2 => fun _ => nil
  | insn_fptoui id typ1 v1 typ2 => fun _ => nil
  | insn_fptosi id typ1 v1 typ2 => fun _ => nil
  | insn_uitofp id typ1 v1 typ2 => fun _ => nil
  | insn_sitofp id typ1 v1 typ2 => fun _ => nil
  | insn_ptrtoint id typ1 v1 typ2 => fun _ => nil
  | insn_inttoptr id typ1 v1 typ2 =>fun _ => nil
  | insn_bitcast id typ1 v1 typ2 => fun _ => nil
  | insn_icmp id cond typ v1 v2 => fun _ => nil
  | insn_fcmp id cond typ v1 v2 => fun _ => nil
  | insn_phi id typ idls => genBlockUseDef_phi_cases idls i b f m
  end.
 
  Fixpoint genBlockUseDef_insns (is:list_insn) (b:block) (f:fdef) (m:module) : usedef_block :=
  match is with
  | nil => fun _ => nil
  | i::is' => (genBlockUseDef_insn i b f m)++++(genBlockUseDef_insns is' b f m)
  end.  

  Definition genBlockUseDef_block (b:block) (f:fdef) (m:module) : usedef_block :=
  match b with
  | block_def l is => genBlockUseDef_insns is b f m
  end.  

  Fixpoint genBlockUseDef_blocks (bs:list_block) (f:fdef) (m:module) : usedef_block :=
  match bs with 
  | nil => fun _ => nil
  | b::bs' => (genBlockUseDef_blocks bs' f m)++++(genBlockUseDef_block b f m)
  end.

  Definition genBlockUseDef_fdef (f:fdef) (m:module) : usedef_block := 
  match f with
  | fdef_intro fheader blocks => genBlockUseDef_blocks blocks f m 
  end.

  Fixpoint genBlockUseDef (m: module) : usedef_block :=
  match m with 
  | module_nil => fun _ => nil
  | module_global_var m' g => genBlockUseDef m'
  | module_function_def m' f => (genBlockUseDef m') ++++ (genBlockUseDef_fdef f m)
  | module_function_dec m' f => genBlockUseDef m'
  | module_namedtype m' nt => genBlockUseDef m'
  end.

End UseDef.



Section CFG.

  Definition getTerminator (b:block) : option insn := 
  match b with
  | block_def l is => last_opt insn is
  end. 

  Fixpoint getLabelsFromSwitchCases (cs:list (const*l)) : ls :=
  match cs with
  | nil => empty_set l
  | (_, l0)::cs' => set_add eq_nat_dec l0 (getLabelsFromSwitchCases cs')
  end.

  Definition getLabelsFromTerminator (i:insn) : ls := 
  match i with
  | insn_br v l1 l2 => set_add eq_nat_dec l1 (set_add eq_nat_dec l2 (empty_set l))
  | insn_br_uncond l0 => set_add eq_nat_dec l0 (empty_set l) 
  | insn_switch v l0 cls => set_add eq_nat_dec l0 (getLabelsFromSwitchCases cls)
  | insn_invoke id id0 ps l1 l2 => set_add eq_nat_dec l1 (set_add eq_nat_dec l2 (empty_set l))
  | _ => empty_set l
  end.

  Fixpoint getBlocksFromLabels (ls0:ls) (l2b:l2block): list_block :=
  match ls0 with
  | nil => nil
  | l0::ls0' => 
    match (l2b l0) with
    | None => getBlocksFromLabels ls0' l2b
    | Some b => b::getBlocksFromLabels ls0' l2b
    end
  end.

  Definition succOfBlock (b:block) (m:module) : list_block :=
  match (getTerminator b) with
  | None => nil
  | Some i => getBlocksFromLabels (getLabelsFromTerminator i) (genBlock2Label m)
  end.
  
  Fixpoint predOfBlock_rec (ls:list (prod insn block)) : list_block :=
  match ls with
  | nil => nil
  | (i, b)::ls' => b::predOfBlock_rec ls'
  end.

  Definition predOfBlock (b:block) (udb:usedef_block) : list_block :=
  predOfBlock_rec (udb b).

End CFG.

Section Dominator.

  Parameter genDominatorTree : fdef -> dt.
  Parameter blockDominates : dt -> block -> block -> Prop.
  Parameter insnDominates : dt -> insn -> insn -> Prop.

End Dominator.

(*ENDCOPY*)

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "./ott") ***
*** End: ***
 *)
