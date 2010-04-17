
Require Import ssa_def.

(*BEGINCOPY*)

Require Import List.
Require Import ListSet.
Require Import Bool.
Require Import Arith.
Require Import Compare_dec.
Require Import Recdef.
Require Import Coq.Program.Wf.
Require Import Omega.

(**********************************)
(* LabelSet. *)

  Definition lempty_set := empty_set l.
  Definition lset_add (l1:l) (ls2:ls) := set_add eq_nat_dec l1 ls2.
  Definition lset_union (ls1 ls2:ls) := set_union eq_nat_dec ls1 ls2.
  Definition lset_inter (ls1 ls2:ls) := set_inter eq_nat_dec ls1 ls2.
  Definition lset_eq (ls1 ls2:ls) := 
    match (lset_inter ls1 ls2) with
    | nil => true
    | _ => false
    end.
  Definition lset_neq (ls1 ls2:ls) := 
    match (lset_inter ls1 ls2) with
    | nil => false
    | _ => true
    end.
  Definition lset_single (l0:l) := lset_add l0 (lempty_set). 
  Definition lset_mem (l0:l) (ls0:ls) := set_mem eq_nat_dec l0 ls0.


(**********************************)
(* SSA. *)

  Definition l2block := l -> option block.

  Definition mergel2block (lb1:l2block) (lb2:l2block) : l2block :=
  fun l0 =>
  match (lb1 l0, lb2 l0) with
  | (Some b1, _) => Some b1
  | (_, Some b2) => Some b2
  | (_, _) => None 
  end.

  Definition genLabel2Block_block (b:block) (f:fdef) (m:module) : l2block :=
  match b with
  | block_intro l _ => fun l' => 
    match lt_eq_lt_dec l' l with 
    | inleft (right _) => Some b
    | _ => None
    end 
  end.  

  Fixpoint genLabel2Block_blocks (bs:list_block) (f:fdef) (m:module) : l2block :=
  match bs with 
  | nil => fun _ => None
  | b::bs' => mergel2block (genLabel2Block_blocks bs' f m) (genLabel2Block_block b f m)
  end.

  Definition genLabel2Block_fdef (f:fdef) (m:module) : l2block := 
  match f with
  | fdef_intro fheader blocks => genLabel2Block_blocks blocks f m 
  end.

  Fixpoint genLabel2Block_product (p:product) (m: module) : l2block :=
  match p with 
  (*  | product_global_var g => fun _ => None *)
  | product_function_def f => (genLabel2Block_fdef f m)
  | product_function_dec f => fun _ => None 
  (*  | product_namedtype nt => fun _ => None *)
  end.

  Fixpoint genLabel2Block_products (ps:list_product) (m:module) : l2block :=
  match ps with
  | nil => fun _ => None
  | p::ps' => mergel2block (genLabel2Block_products ps' m) (genLabel2Block_product p m)
  end.

  Definition genLabel2Block (m: module) : l2block :=
  genLabel2Block_products m m.

  Definition getEntryOfFdef (f:fdef) : option block :=
  match f with
  | fdef_intro fheader blocks => 
    match blocks with
    | nil => None
    | b::blocks' => Some b
    end 
  end.  

  Definition getNonEntryOfFdef (f:fdef) : list_block :=
  match f with
  | fdef_intro fheader blocks => 
    match blocks with
    | nil => nil
    | b::blocks' => blocks'
    end 
  end.  

  Definition lookupBlockViaLabelFromModule (m:module) (l0:l) : option block :=
  genLabel2Block m l0.  

  Fixpoint lookupBlockViaLabelFromSystem (s:system) (l0:l) : option block :=
  match s with 
  | nil => None
  | m::s' =>
    match (genLabel2Block m l0) with
    | Some b => Some b
    | None => lookupBlockViaLabelFromSystem s' l0
    end  
  end.

  Fixpoint getLabelsFromBlocks (lb:list_block) : ls :=
  match lb with
  | nil => lempty_set
  | (block_intro l0 _)::lb' => lset_add l0 (getLabelsFromBlocks lb')
  end.

(**********************************)
(* UseDef *)

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
  | insn_br t v l1 l2 => None
  | insn_br_uncond l => None
  (* | insn_switch t v l _ => None *)
  | insn_invoke id typ id0 paraml l1 l2 => Some id
  | insn_call id typ id0 paraml => Some id
  | insn_unreachable => None
  | insn_add id typ v1 v2 => Some id
  (* | insn_fadd id typ v1 v2 => Some id *)
  (* | insn_udiv id typ v1 v2 => Some id *)
  (* | insn_fdiv id typ v1 v2 => Some id *)
  (* | insn_or id typ v1 v2 => Some id *)
  (* | insn_and id typ v1 v2 =>Some id *)
  (* | insn_extractelement id typ0 id0 c1 => Some id *)
  (* | insn_insertelement id typ0 id0 typ1 v1 c2 => Some id *)
  (* | insn_extractvalue id typs id0 c1 => Some id *)
  (* | insn_insertvalue id typs id0 typ1 v1 c2 => Some id *)
  (* | insn_alloca id typ N => None *)
  (* | insn_load id typ1 id1 => Some id *)
  (* | insn_store typ1 v1 typ2 id2 => None *)
  (* | insn_trunc id typ1 v1 typ2 => Some id *)
  (* | insn_fptrunc id typ1 v1 typ2 =>Some id *)
  (* | insn_fptoui id typ1 v1 typ2 => Some id *)
  (* | insn_fptosi id typ1 v1 typ2 =>Some id *)
  (* | insn_uitofp id typ1 v1 typ2 =>Some id *)
  (* | insn_sitofp id typ1 v1 typ2 =>Some id *)
  (* | insn_ptrtoint id typ1 v1 typ2 => Some id *)
  (* | insn_inttoptr id typ1 v1 typ2 => Some id *)
  (* | insn_bitcast id typ1 v1 typ2 => Some id *)
  (* | insn_icmp id cond typ v1 v2 => Some id *)
  (* | insn_fcmp id cond typ v1 v2 => Some id *)
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
    | inleft (right _) => i::nil
    | _ => nil
    end 
  |( _, _) => nil
  end.     

  Definition genInsnUseDef_id (id0:id) (i:insn) (b:block) (f:fdef) (m:module) : usedef_insn :=
  fun i' => 
  match (getInsnID i') with
  | Some id' => 
    match lt_eq_lt_dec id' id0 with 
    | inleft (right _) => i::nil
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
  | insn_br t v l1 l2 => genInsnUseDef_value v i b f m        
  | insn_br_uncond l => fun _ => nil
  (* | insn_switch t v l _ => genInsnUseDef_value v i b f m *)
  | insn_invoke id typ id0 paraml l1 l2 => (genInsnUseDef_id id0 i b f m)+++(genInsnUseDef_params paraml i b f m)
  | insn_call id typ id0 paraml => fun _ => nil
  | insn_unreachable => fun _ => nil
  | insn_add id typ v1 v2 => (genInsnUseDef_value v1 i b f m)+++(genInsnUseDef_value v2 i b f m)
  (* | insn_fadd id typ v1 v2 => (genInsnUseDef_value v1 i b f m)+++(genInsnUseDef_value v2 i b f m) 	 *)
  (* | insn_udiv id typ v1 v2 => (genInsnUseDef_value v1 i b f m)+++(genInsnUseDef_value v2 i b f m)  *)
  (* | insn_fdiv id typ v1 v2 => (genInsnUseDef_value v1 i b f m)+++(genInsnUseDef_value v2 i b f m)  *)
  (* | insn_or id typ v1 v2 => (genInsnUseDef_value v1 i b f m)+++(genInsnUseDef_value v2 i b f m)  *)
  (* | insn_and id typ v1 v2 => (genInsnUseDef_value v1 i b f m)+++(genInsnUseDef_value v2 i b f m)  *)
  (* | insn_extractelement id typ0 value0 c1 =>  *)
  (*   (genInsnUseDef_value value0 i b f m) *)
  (* | insn_insertelement id typ0 value0 typ1 v1 c2 =>  *)
  (*   (genInsnUseDef_value value0 i b f m)+++(genInsnUseDef_value v1 i b f m) *)
  (* | insn_extractvalue id typ0 value0 c1 =>  *)
  (*   (genInsnUseDef_value value0 i b f m) *)
  (* | insn_insertvalue id typs value0 typ1 v1 c2 =>  *)
  (*   (genInsnUseDef_value value0 i b f m)+++(genInsnUseDef_value v1 i b f m) *)
  (* | insn_alloca id typ N => fun _ => nil *)
  (* | insn_load id typ1 v1 => genInsnUseDef_value v1 i b f m *)
  (* | insn_store typ1 v1 typ2 v2 => (genInsnUseDef_value v1 i b f m)+++(genInsnUseDef_value v2 i b f m)	  *)
  (* | insn_trunc id typ1 v1 typ2 => (genInsnUseDef_value v1 i b f m)			 *)
  (* | insn_fptrunc id typ1 v1 typ2 => (genInsnUseDef_value v1 i b f m)			 *)
  (* | insn_fptoui id typ1 v1 typ2 => (genInsnUseDef_value v1 i b f m)			 *)
  (* | insn_fptosi id typ1 v1 typ2 => (genInsnUseDef_value v1 i b f m)			 *)
  (* | insn_uitofp id typ1 v1 typ2 => (genInsnUseDef_value v1 i b f m)			 *)
  (* | insn_sitofp id typ1 v1 typ2 => (genInsnUseDef_value v1 i b f m)			 *)
  (* | insn_ptrtoint id typ1 v1 typ2 => (genInsnUseDef_value v1 i b f m)			 *)
  (* | insn_inttoptr id typ1 v1 typ2 => (genInsnUseDef_value v1 i b f m)			 *)
  (* | insn_bitcast id typ1 v1 typ2 => (genInsnUseDef_value v1 i b f m)			 *)
  (* | insn_icmp id cond typ v1 v2 => (genInsnUseDef_value v1 i b f m)+++(genInsnUseDef_value v2 i b f m)  *)
  (* | insn_fcmp id cond typ v1 v2 => (genInsnUseDef_value v1 i b f m)+++(genInsnUseDef_value v2 i b f m)  *)
  | insn_phi id typ idls => fun _ => nil
  end.
 
  Fixpoint genInsnUseDef_insns (is:list_insn) (b:block) (f:fdef) (m:module) : usedef_insn :=
  match is with
  | nil => fun _ => nil
  | i::is' => (genInsnUseDef_insn i b f m)+++(genInsnUseDef_insns is' b f m)
  end.  

  Definition genInsnUseDef_block (b:block) (f:fdef) (m:module) : usedef_insn :=
  match b with
  | block_intro l is => genInsnUseDef_insns is b f m
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

  Fixpoint genInsnUseDef_product (p:product) (m: module) : usedef_insn :=
  match p with 
  (* | product_global_var g => fun _ => nil *)
  | product_function_def f => (genInsnUseDef_fdef f m)
  | product_function_dec f => fun _ => nil
  (* | product_namedtype nt => fun _ => nil *)
  end.

  Fixpoint genInsnUseDef_products (ps:list_product) (m:module) : usedef_insn :=
  match ps with
  | nil => fun _ => nil
  | p::ps' => (genInsnUseDef_products ps' m) +++ (genInsnUseDef_product p m) 
  end.

  Definition genInsnUseDef (m: module) : usedef_insn :=
  genInsnUseDef_products m m.

  Definition getInsnUseDef (udi:usedef_insn) (i:insn) : list_insn :=
  udi i. 

  (* generate block use-def *)

  Definition getBlockLabel (b:block) : l :=
  match b with
  | block_intro l b => l
  end.

  Definition genBlockUseDef_label (l0:l) (i:insn) (b:block) (f:fdef) (m:module) : usedef_block :=
  fun b' => 
  match lt_eq_lt_dec (getBlockLabel b') l0 with 
  | inleft (right _) => b::nil
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
  | insn_br t v l1 l2 => genBlockUseDef_label l1 i b f m ++++ genBlockUseDef_label l2 i b f m       
  | insn_br_uncond l => genBlockUseDef_label l i b f m
  (* | insn_switch t v l ls => genBlockUseDef_label l i b f m ++++ genBlockUseDef_switch_cases ls i b f m *)
  | insn_invoke id typ id0 paraml l1 l2 => (genBlockUseDef_label l1 i b f m)++++(genBlockUseDef_label l2 i b f m)
  | insn_call id typ id0 paraml => fun _ => nil
  | insn_unreachable => fun _ => nil 
  | insn_add id typ v1 v2 => fun _ => nil 
  (* | insn_fadd id typ v1 v2 => fun _ => nil *)
  (* | insn_udiv id typ v1 v2 => fun _ => nil *)
  (* | insn_fdiv id typ v1 v2 => fun _ => nil *)
  (* | insn_or id typ v1 v2 => fun _ => nil *)
  (* | insn_and id typ v1 v2 => fun _ => nil *)
  (* | insn_extractelement id typ0 v0 c1 => fun _ => nil *)
  (* | insn_insertelement id typ0 v0 typ1 v1 c2 => fun _ => nil *)
  (* | insn_extractvalue id typ0 v0 c1 => fun _ => nil *)
  (* | insn_insertvalue id typ0 v0 typ1 v1 c2 => fun _ => nil *)
  (* | insn_alloca id typ N => fun _ => nil *)
  (* | insn_load id typ1 v1 => fun _ => nil *)
  (* | insn_store typ1 v1 typ2 v2 => fun _ => nil *)
  (* | insn_trunc id typ1 v1 typ2 => fun _ => nil *)
  (* | insn_fptrunc id typ1 v1 typ2 => fun _ => nil *)
  (* | insn_fptoui id typ1 v1 typ2 => fun _ => nil *)
  (* | insn_fptosi id typ1 v1 typ2 => fun _ => nil *)
  (* | insn_uitofp id typ1 v1 typ2 => fun _ => nil *)
  (* | insn_sitofp id typ1 v1 typ2 => fun _ => nil *)
  (* | insn_ptrtoint id typ1 v1 typ2 => fun _ => nil *)
  (* | insn_inttoptr id typ1 v1 typ2 =>fun _ => nil *)
  (* | insn_bitcast id typ1 v1 typ2 => fun _ => nil *)
  (* | insn_icmp id cond typ v1 v2 => fun _ => nil *)
  (* | insn_fcmp id cond typ v1 v2 => fun _ => nil *)
  | insn_phi id typ idls => genBlockUseDef_phi_cases idls i b f m
  end.
 
  Fixpoint genBlockUseDef_insns (is:list_insn) (b:block) (f:fdef) (m:module) : usedef_block :=
  match is with
  | nil => fun _ => nil
  | i::is' => (genBlockUseDef_insn i b f m)++++(genBlockUseDef_insns is' b f m)
  end.  

  Definition genBlockUseDef_block (b:block) (f:fdef) (m:module) : usedef_block :=
  match b with
  | block_intro l is => genBlockUseDef_insns is b f m
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

  Fixpoint genBlockUseDef_product (p:product) (m: module) : usedef_block :=
  match p with 
  (* | product_global_var g => fun _ => nil *)
  | product_function_def f => (genBlockUseDef_fdef f m)
  | product_function_dec f => fun _ => nil
  (* | product_namedtype nt => fun _ => nil *)
  end.

  Fixpoint genBlockUseDef_products (ps:list_product) (m:module) : usedef_block :=
  match ps with
  | nil => fun _ => nil
  | p::ps' => (genBlockUseDef_products ps' m) ++++ (genBlockUseDef_product p m) 
  end.

  Definition genBlockUseDef (m: module) : usedef_block :=
  genBlockUseDef_products m m.

  Definition getBlockUseDef (udb:usedef_block) (b:block) : list_block :=
  udb b. 

(**********************************)
(* CFG. *)

  Definition getTerminator (b:block) : option insn := 
  match b with
  | block_intro l is => last_opt insn is
  end. 

  Fixpoint getLabelsFromSwitchCases (cs:list (const*l)) : ls :=
  match cs with
  | nil => lempty_set 
  | (_, l0)::cs' => lset_add l0 (getLabelsFromSwitchCases cs')
  end.

  Definition getLabelsFromTerminator (i:insn) : ls := 
  match i with
  | insn_br t v l1 l2 => lset_add l1 (lset_add l2 lempty_set)
  | insn_br_uncond l0 => lset_add l0 lempty_set 
  (* | insn_switch t v l0 cls => lset_add l0 (getLabelsFromSwitchCases cls) *)
  | insn_invoke id typ id0 ps l1 l2 => lset_add l1 (lset_add l2 lempty_set)
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
  | Some i => getBlocksFromLabels (getLabelsFromTerminator i) (genLabel2Block m)
  end.
  
  Fixpoint predOfBlock_rec (ls:list block) : list_block :=
  match ls with
  | nil => nil
  | b::ls' => b::predOfBlock_rec ls'
  end.

  Definition predOfBlock (b:block) (udb:usedef_block) : list_block :=
  predOfBlock_rec (udb b).

  Definition hasSinglePredecessor (b:block) (udb:usedef_block) : bool :=
  match (eq_nat_dec (length (predOfBlock b udb)) 1) with
  | left _ => true
  | right _ => false
  end.

(**********************************)
(* Dominator. *)

  Parameter genLabelsFromFdef : fdef -> ls.

  Fixpoint inputFromPred (bs:list_block) (output:dt) : ls :=
  match bs with
  | nil => lempty_set
  | (block_intro l0 _)::bs' => lset_union (output l0) (inputFromPred bs' output)
  end.

  Definition outputFromInput (b:block) (input:ls) : ls :=
  match b with
  | block_intro l0 _ => lset_add l0 input
  end.

  Definition update_dt (d1:dt) (l0:l) (ls0:ls) : dt :=
  fun l1 =>
  match lt_eq_lt_dec l1 l0 with 
  | inleft (right _) => ls0
  | _ => d1 l1
  end. 

  Definition inter_dt (d1 d2:dt) : dt :=
  fun l0 => lset_inter (d1 l0) (d2 l0).

  Fixpoint genDominatorTree_blocks_innerloop (bs:list_block) (udb:usedef_block) (output:dt) : dt :=
  match bs with 
  | nil => output
  | (block_intro l is)::bs' => 
    match (outputFromInput (block_intro l is) (inputFromPred (predOfBlock (block_intro l is) udb) output)) with 
    | ls' => genDominatorTree_blocks_innerloop bs' udb (update_dt output l ls') 
    end
(*  | (block_without_label is)::bs' => 
    genDominatorTree_blocks_innerloop bs' udb output  *)
  end.  

  (*
    Check if the two dominator tress are equal w.r.t the domain (blocks of the current function)
  *)
  Fixpoint eq_dt (d0 d1:dt) (bs:list_block) : bool :=
  match bs with
  | nil => true
  | (block_intro l0 _)::bs' =>
    match (lset_eq (d0 l0) (d1 l0)) with
    | true => eq_dt d0 d1 bs'
    | false => false
    end
(*  | _::bs' => eq_dt d0 d1 bs' *)
  end.

  Fixpoint sizeOfDT (bs:list_block) (output:dt) : nat :=
  match bs with
  | nil => 0
  | (block_intro l0 _)::bs' => length (output l0) + sizeOfDT bs' output
(*  | _::bs'=> sizeOfDT bs' output *)
  end.

  Definition size (arg:(list_block*dt)) : nat :=
  match arg with
  | (bs, output) => sizeOfDT bs output
  end.

  Function genDominatorTree_blocks (arg:list_block*dt) (udb:usedef_block) {measure size arg} : dt :=
  match arg with
  | (bs, output) => 
    match (genDominatorTree_blocks_innerloop bs udb output) with
    | output' =>
      match (eq_dt output output' bs) with
      | true => output'
      | false => genDominatorTree_blocks (bs, output') udb
      end
    end
  end.
  intros.
  Admitted.

  Fixpoint initialize_genDominatorTree_blocks (bs:list_block) (U:ls) (d0:dt) : dt :=
  match bs with
  | nil => d0
  | (block_intro l0 _)::bs' => initialize_genDominatorTree_blocks bs' U (update_dt d0 l0 U)
(*  | _::bs' => initialize_genDominatorTree_blocks bs' U d0 *)
  end.

  Definition genEmptyDT : dt := fun _ => nil. 

  Definition initialize_genDominatorTree_entry (f:fdef) : dt :=
  match (getEntryOfFdef f) with
  | None => genEmptyDT
  | Some (block_intro l0 _) => update_dt genEmptyDT l0 (lset_single l0)
(*  | Some  _ => genEmptyDT *)
  end.

  Definition initialize_genDominatorTree (f:fdef) (U:ls) : dt :=
  initialize_genDominatorTree_blocks (getNonEntryOfFdef f) U (initialize_genDominatorTree_entry f).  

  Definition genDominatorTree (f:fdef) (m:module) : dt :=
  match f with
  | fdef_intro fheader blocks => 
    genDominatorTree_blocks (blocks, (initialize_genDominatorTree f (genLabelsFromFdef f))) (genBlockUseDef m)  
  end.

  Definition blockDominates (d:dt) (b1 b2: block) : Prop :=
  match b1 with
  | block_intro l1 _ =>
    match (d l1) with
    | ls1 => 
      match b2 with
      | block_intro l2 _ => 
        match (lset_mem l2 ls1) with
        | true => True
        | false => False
        end
(*      | _ => False *)
      end
    end 
(*  | _ => False *)
  end.

  Definition blockDominatesB (d:dt) (b1 b2: block) : bool :=
  match b1 with
  | block_intro l1 _ =>
    match (d l1) with
    | ls1 => 
      match b2 with
      | block_intro l2 _ => 
        match (lset_mem l2 ls1) with
        | true => true
        | false => false
        end
(*      | _ => false *)
      end
    end 
(*  | _ => false *)
  end.

  Definition insnDominates (i1 i2:insn) : Prop :=
  match (getInsnID i1, getInsnID i2) with
  | (Some id1, Some id2) =>
    match (le_lt_dec id1 id2) with
    | left _ => (*id1 <= id2*) True
    | right _ => (*id2 < id2*) False
    end
  | _ => False
  end.

  Definition insnDominatesB (i1 i2:insn) : bool :=
  match (getInsnID i1, getInsnID i2) with
  | (Some id1, Some id2) =>
    match (le_lt_dec id1 id2) with
    | left _ => (*id1 <= id2*) true
    | right _ => (*id2 < id2*) false
    end
  | _ => false
  end.

  Definition isReachableFromEntry (fi:fdef_info) (b:block) : Prop :=
  let (f, d) := fi in   
  match (getEntryOfFdef f) with
  | None => False
  | Some be => blockDominates d be b
  end.
 
  Definition isReachableFromEntryB (fi:fdef_info) (b:block) : bool :=
  let (f, d) := fi in   
  match (getEntryOfFdef f) with
  | None => false
  | Some be => blockDominatesB d be b
  end.

(**********************************)
(* Classes. *)

Definition isPointerTypB (t:typ) : bool :=
match t with
| typ_pointer _ => true
| _ => false
end.

Definition isArrayTypB (t:typ) : bool :=
match t with
| typ_array _ _ => true
| _ => false
end.

Definition isInvokeInsnB (i:insn) : bool :=
match i with
| insn_invoke _ _ _ _ _ _ => true
| _ => false
end.

Definition isCallInsnB (i:insn) : bool :=
match i with
| insn_call _ _ _ _ => true
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
| typ_function _ _ => true
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
| typ_function _ _ => true
| _ => false
end.

Definition isValidElementTypB (t:typ) : bool :=
negb (isNotValidElementTypB t).

Definition isPhiNodeB (i:insn) : bool :=
match i with
| insn_phi _ _ _ => true
| _ => false
end.

Definition isTerminatorInsnB (i:insn) : bool :=
match i with
| insn_return _ _ => true
| insn_return_void => true
| insn_br _ _ _ _ => true
| insn_br_uncond _ => true
(* | insn_switch _ _ _ => true *)
| insn_invoke _ _ _ _ _ _ => true
| insn_unreachable => true
| _ => false
end.

Definition isBindingFdecB (ib:id_binding) : bool :=
match ib with
| id_binding_fdec fdec => true
| _ => false
end.

Definition isBindingArgB (ib:id_binding) : bool :=
match ib with
| id_binding_arg arg => true
| _ => false
end.

Definition isBindingInsnB (ib:id_binding) : bool :=
match ib with
| id_binding_insn _ => true
| _ => false
end.

(**********************************)
(* Inversion. *)

Definition getInsnTypC (i:insn) : option typ :=
match i with
| insn_return typ _ => Some typ
| insn_return_void => None
| insn_br typ _ _ _ => None 
| insn_br_uncond _ => None
(* | insn_switch typ _ _ _ => None *)
| insn_invoke _ typ _ _ _ _ => Some typ
| insn_call _ typ _ _ => Some typ
| insn_unreachable => None
| insn_add _ typ _ _ => Some typ
(*| insn_fadd _ typ _ _ => Some typ
| insn_udiv _ typ _ _ => Some typ
| insn_fdiv _ typ _ _ => Some typ
| insn_or _ typ _ _ => Some typ
| insn_and _ typ _ _ => Some typ
| insn_extractelement _ typ _ _ => getElementTyp typ
| insn_insertelement _ typ _ _ _ _ => typ
| insn_extractvalue _ typ _ const1 => getFieldTyp typ const1
| insn_insertvalue _ typ _ _ _ _ => typ
| insn_alloca _ typ _ => Some (typ_pointer typ)
| insn_load _ typ _ => getLoadTyp typ
| insn_store _ _ _ _ => None
| insn_trunc _ _ _ typ => Some typ
| insn_fptrunc _ _ _ typ => Some typ
| insn_fptoui _ _ _ typ => Some typ
| insn_fptosi _ _ _ typ => Some typ
| insn_uitofp _ _ _ typ => Some typ
| insn_sitofp _ _ _ typ => Some typ
| insn_ptrtoint _ _ _ typ => Some typ
| insn_inttoptr _ _ _ typ => Some typ
| insn_bitcase _ _ _ typ => Some typ
| insn_icmp _ _ _ _ _ => Some (typ_int 1)
| insn_fcmp _ _ _ _ _ => Some (typ_int 1) *)
| insn_phi _ typ _ => Some typ
end.

Definition getPointerEltTypC (t:typ) : option typ :=
match t with
| typ_pointer t' => Some t' 
| _ => None
end.

Definition getValueIDsC (v:value) : ids :=
match (getValueID v) with
| None => nil
| Some id => id::nil
end.

Fixpoint getParamsOperandC (lp:list_param) : ids :=
match lp with
| nil => nil
| (t, v)::lp' => (getValueIDsC v) ++ (getParamsOperandC lp')
end.

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

Definition getInsnOperandsC (i:insn) : ids :=
match i with
| insn_return _ v => getValueIDsC v
| insn_return_void => nil
| insn_br _ v _ _ => getValueIDsC v
| insn_br_uncond _ => nil
(* | insn_switch _ value _ _ => getValueIDs value *)
| insn_invoke _ _ _ lp _ _ => getParamsOperandC lp
| insn_call _ _ _ lp => getParamsOperandC lp
| insn_unreachable => nil
| insn_add _ _ v1 v2 => getValueIDsC v1 ++ getValueIDsC v2
(*| insn_fadd _ _ v1 v2 => getValueIDsC v1 ++ getValueIDsC v2
| insn_udiv _ _ v1 v2 => getValueIDsC v1 ++ getValueIDsC v2
| insn_fdiv _ _ v1 v2 => getValueIDsC v1 ++ getValueIDsC v2
| insn_or _ _ v1 v2 => getValueIDsC v1 ++ getValueIDsC v2
| insn_and _ _ v1 v2 => getValueIDsC v1 ++ getValueIDsC v2
| insn_extractelement _ _ v _ => getValueIDsC v
| insn_insertelement _ _ v1 _ v2 _ => getValueIDsC v1 ++ getValueIDsC v2
| insn_extractvalue _ _ v _ => getValueIDsC v
| insn_insertvalue _ _ v1 _ v2 _ => getValueIDsC v1 ++ getValueIDsC v2
| insn_alloca _ _ _ => nil
| insn_load _ _ v => getValueIDsC v
| insn_store _ v1 _ v2 => getValueIDsC v1 ++ getValueIDsC v2
| insn_trunc _ _ v _ => getValueIDsC v
| insn_fptrunc _ _ v _ => getValueIDsC v
| insn_fptoui _ _ v _ => getValueIDsC v
| insn_fptosi _ _ v _ => getValueIDsC v
| insn_uitofp _ _ v _ => getValueIDsC v
| insn_sitofp _ _ v _ => getValueIDsC v
| insn_ptrtoint _ _ v _ => getValueIDsC v
| insn_inttoptr _ _ v _ => getValueIDsC v
| insn_bitcase _ _ v _ => getValueIDsC v
| insn_icmp _ _ _ v1 v2 => getValueIDsC v1 ++ getValueIDsC v2
| insn_fcmp _ _ _ v1 v2 => getValueIDsC v1 ++ getValueIDsC v2 *)
| insn_phi _ _ ls => list_prj1 _ _ ls
end.

Definition getInsnLabelsC (i:insn) : ls :=
match i with
| insn_return _ _ => nil
| insn_return_void => nil
| insn_br _ _ l1 l2 => l1::l2::nil
| insn_br_uncond l => l::nil
(* | insn_switch _ _ l ls => l::list_prj2 _ _ ls *)
| insn_invoke _ _ _ _ l1 l2 => l1::l2::nil
| insn_call _ _ _ _ => nil
| insn_unreachable => nil
| insn_add _ _ _ _ => nil
(*| insn_fadd _ _ _ _ => nil
| insn_udiv _ _ _ _ => nil
| insn_fdiv _ _ _ _ => nil
| insn_or _ _ _ _ => nil
| insn_and _ _ _ _ => nil
| insn_extractelement _ _ _ _ => nil
| insn_insertelement _ _ _ _ _ _ => nil
| insn_extractvalue _ _ _ _ => nil
| insn_insertvalue _ _ _ _ _ _ => nil
| insn_alloca _ _ _ => nil
| insn_load _ _ _ => nil
| insn_store _ _ _ _ => nil
| insn_trunc _ _ _ _ => nil
| insn_fptrunc _ _ _ _ => nil
| insn_fptoui _ _ _ _ => nil
| insn_fptosi _ _ _ _ => nil
| insn_uitofp _ _ _ _ => nil
| insn_sitofp _ _ _ _ => nil
| insn_ptrtoint _ _ _ _ => nil
| insn_inttoptr _ _ _ _ => nil
| insn_bitcase _ _ _ _ => nil
| insn_icmp _ _ _ _ _ => nil
| insn_fcmp _ _ _ _ _ => nil *)
| insn_phi _ _ ls => list_prj2 _ _ ls
end.

Fixpoint args2TypsC (la:list_arg) : list_typ :=
match la with
| nil => nil
| (t, id)::la' => t::args2TypsC la'
end.

Definition getFheaderTypC (fh:fheader) : typ :=
match fh with
| fheader_intro t _ la => typ_function t (args2TypsC la)
end.

Definition getFdecTypC (fdec:fdec) : typ :=
match fdec with
| fdec_intro fheader => getFheaderTypC fheader
end.

Definition getFdefTypC (fdef:fdef) : typ :=
match fdef with
| fdef_intro fheader _ => getFheaderTypC fheader
end.

Definition getBindingTypC (ib:id_binding) : option typ :=
match ib with
| id_binding_insn i => getInsnTypC i
(* | id_binding_g _ t _ => Some t *)
| id_binding_arg (t, id) => Some t
| id_binding_fdec fdec => Some (getFdecTypC fdec)
| id_binding_none => None
end.

Definition getInsnsFromBlockC (b:block) : list_insn :=
match b with
| block_intro l li => li
(* | block_without_label li => li *)
end.

Definition getBindingFdecC (ib:id_binding) : option fdec :=
match ib with
| id_binding_fdec fdec => Some fdec
| _ => None
end.

Definition getBindingArgC (ib:id_binding) : option arg :=
match ib with
| id_binding_arg arg => Some arg
| _ => None
end.

(*
Definition getBindingGC (ib:id_binding) : option g :=
match ib with
| id_binding_g g => Some g
| _ => None
end.
*)

Definition getBindingInsnC (ib:id_binding) : option insn :=
match ib with
| id_binding_insn i => Some i
| _ => None
end.

Definition getFheaderIDC (fh:fheader) : id :=
match fh with
| fheader_intro _ id _ => id
end.

Definition getFdecIDC (fd:fdec) : id :=
match fd with
| fdec_intro fh => getFheaderIDC fh
end.

Definition getFdefIDC (fd:fdef) : id :=
match fd with
| fdef_intro fh _ => getFheaderIDC fh
end.

Definition getNormalDestFromInvokeInsnC (i:insn) : option l :=
match i with
| insn_invoke _ _ _ _ l1 _ => Some l1
| _ => None
end.

Definition getUnwindDestFromInvokeInsnC (i:insn) : option l :=
match i with
| insn_invoke _ _ _ _ _ l2 => Some l2
| _ => None
end.

Fixpoint getLabelViaIDFromList (ls:list (id*l)) (branch:id) : option l :=
match ls with
| nil => None
| (id, l)::ls' => 
  match (eq_nat_dec id branch) with
  | left _ => Some l
  | right _ => getLabelViaIDFromList ls' branch
  end
end.

Definition getLabelViaIDFromPhiNode (phi:insn) (branch:id) : option l :=
match phi with
| insn_phi _ _ ls => getLabelViaIDFromList ls branch
| _ => None
end.

Fixpoint getLabelsFromIdls (idls:list (id*l)) : ls :=
match idls with
| nil => lempty_set
| (_, l)::idls' => lset_add l (getLabelsFromIdls idls')
end.

Definition getLabelsFromPhiNodeC (phi:insn) : ls :=
match phi with
| insn_phi _ _ ls => getLabelsFromIdls ls
| _ => lempty_set
end.

(**********************************)
(* Lookup. *)

(* ID binding lookup *)

Definition lookupBindingViaIDFromInsnC (i:insn) (id:id) : id_binding :=
match (getInsnID i) with
| None => id_binding_none
| Some id' =>
  match (eq_nat_dec id id') with
  | left _ => id_binding_insn i
  | right _ => id_binding_none
  end
end.

Fixpoint lookupBindingViaIDFromInsnsC (li:list_insn) (id:id) : id_binding :=
match li with
| nil => id_binding_none
| i::li' =>
  match (lookupBindingViaIDFromInsnC i id) with
  | id_binding_insn _ => id_binding_insn i
  | _ => lookupBindingViaIDFromInsnsC li' id
  end
end.

Definition lookupBindingViaIDFromBlockC (b:block) (id:id) : id_binding :=
let list_insn := getInsnsFromBlockC b in
lookupBindingViaIDFromInsnsC list_insn id.

Fixpoint lookupBindingViaIDFromBlocksC (lb:list_block) (id:id) : id_binding :=
match lb with
| nil => id_binding_none
| b::lb' => 
  match (lookupBindingViaIDFromBlockC b id) with
  | id_binding_insn i => id_binding_insn i
  | _ => lookupBindingViaIDFromBlocksC lb' id
  end
end.

Definition lookupBindingViaIDFromArgC (a:arg) (id:id) : id_binding :=
let (t, id') := a in
match (eq_nat_dec id id') with
| left _ => id_binding_arg a
| right _ => id_binding_none
end.

Fixpoint lookupBindingViaIDFromArgsC (la:list_arg) (id:id) : id_binding :=
match la with 
| nil => id_binding_none
| a::la' => 
  match (lookupBindingViaIDFromArgC a id) with
  | id_binding_arg a' => id_binding_arg a'
  | _ => lookupBindingViaIDFromArgsC la' id
  end
end.

Definition lookupBindingViaIDFromFdecC (fd:fdec) (id:id) : id_binding :=
let '(fdec_intro (fheader_intro t id' la)) := fd in
match (eq_nat_dec id id') with
| left _ => id_binding_fdec fd
| right _ => lookupBindingViaIDFromArgsC la id
end.

Definition lookupBindingViaIDFromFdefC (fd:fdef) (id:id) : id_binding :=
let '(fdef_intro fh lb) := fd in
lookupBindingViaIDFromBlocksC lb id.

Definition lookupBindingViaIDFromProductC (p:product) (id:id) : id_binding :=
match p with
(*
| product_global id' t c =>
  match (eq_nat_dec id id') with
  | left _ => id_binding_global id' t c
  | right _ => id_binding_none
  end
*)
| product_function_dec fdec => lookupBindingViaIDFromFdecC fdec id
(* | product_namedt _ => id_binding_none *)
| product_function_def fdef => lookupBindingViaIDFromFdefC fdef id
end.  

Fixpoint lookupBindingViaIDFromProductsC (lp:list_product) (id:id) : id_binding :=
match lp with
| nil => id_binding_none
| p::lp' => 
  match (lookupBindingViaIDFromProductC p id) with
  | id_binding_insn i => id_binding_insn i
  | id_binding_fdec f => id_binding_fdec f
  (* | id_binding_global g => id_binding_global g *)
  | _ => lookupBindingViaIDFromProductsC lp' id
  end
end.
  
Definition lookupBindingViaIDFromModuleC (m:module) (id:id) : id_binding :=
lookupBindingViaIDFromProductsC m id.

Fixpoint lookupBindingViaIDFromModulesC (lm:list_module) (id:id) : id_binding :=
match lm with
| nil => id_binding_none
| m::lm' =>
  match (lookupBindingViaIDFromModuleC m id) with
  | id_binding_insn i => id_binding_insn i
  | id_binding_fdec f => id_binding_fdec f
  (* | id_binding_global g => id_binding_global g *)
  | _ => lookupBindingViaIDFromModulesC lm' id
  end
end.

Definition lookupBindingViaIDFromSystemC (s:system) (id:id) : id_binding :=
lookupBindingViaIDFromModulesC s id.

(* Block lookup from ID *)

Definition isIDInBlockB (id:id) (b:block) : bool :=
match (lookupBindingViaIDFromBlockC b id) with
| id_binding_insn i => true
| _ => false
end.

Fixpoint lookupBlockViaIDFromBlocksC (lb:list_block) (id:id) : option block :=
match lb with
| nil => None  
| b::lb' => 
  match (isIDInBlockB id b) with
  | true => Some b
  | false => lookupBlockViaIDFromBlocksC lb' id
  end
end.

Definition lookupBlockViaIDFromFdefC (fd:fdef) (id:id) : option block :=
match fd with
| fdef_intro fh lb => lookupBlockViaIDFromBlocksC lb id
end.

(* Fun lookup from ID *)

Definition lookupFdecViaIDFromProductC (p:product) (i:id) : option fdec :=
match p with
| (product_function_dec fd) => if beq_nat (getFdecIDC fd) i then Some fd else None
| _ => None
end.

Fixpoint lookupFdecViaIDFromProductsC (lp:list_product) (i:id) : option fdec :=
match lp with
| nil => None
| p::lp' => 
  match (lookupFdecViaIDFromProductC p i) with
  | Some fd => Some fd
  | None => lookupFdecViaIDFromProductsC lp' i
  end
end.

Definition lookupFdecViaIDFromModuleC (m:module) (i:id) : option fdec :=
lookupFdecViaIDFromProductsC m i.

Fixpoint lookupFdecViaIDFromModulesC (lm:list_module) (i:id) : option fdec :=
match lm with
| nil => None
| m::lm' => 
  match (lookupFdecViaIDFromModuleC m i) with
  | Some fd => Some fd
  | None => lookupFdecViaIDFromModulesC lm' i
  end
end.

Definition lookupFdecViaIDFromSystemC (s:system) (i:id) : option fdec :=
lookupFdecViaIDFromModulesC s i.

Definition lookupFdefViaIDFromProductC (p:product) (i:id) : option fdef :=
match p with
| (product_function_def fd) => if beq_nat (getFdefIDC fd) i then Some fd else None
| _ => None
end.

Fixpoint lookupFdefViaIDFromProductsC (lp:list_product) (i:id) : option fdef :=
match lp with
| nil => None
| p::lp' => 
  match (lookupFdefViaIDFromProductC p i) with
  | Some fd => Some fd
  | None => lookupFdefViaIDFromProductsC lp' i
  end
end.

Definition lookupFdefViaIDFromModuleC (m:module) (i:id) : option fdef :=
lookupFdefViaIDFromProductsC m i.

Fixpoint lookupFdefViaIDFromModulesC (lm:list_module) (i:id) : option fdef :=
match lm with
| nil => None
| m::lm' => 
  match (lookupFdefViaIDFromModuleC m i) with
  | Some fd => Some fd
  | None => lookupFdefViaIDFromModulesC lm' i
  end
end.

Definition lookupFdefViaIDFromSystemC (s:system) (i:id) : option fdef :=
lookupFdefViaIDFromModulesC s i.

(*     ID type lookup                                    *)

Definition lookupTypViaIDFromInsnC (i:insn) (id0:id) : option typ :=
match (getInsnTypC i) with
| None => None
| Some t => 
  match (getInsnID i) with
  | None => None
  | Some id0' => 
    if (beq_nat id0 id0') 
    then Some t
    else None
  end
end.

Fixpoint lookupTypViaIDFromInsnsC (li:list_insn) (id0:id) : option typ :=
match li with
| nil => None
| i::li' =>
  match (lookupTypViaIDFromInsnC i id0) with
  | Some t => Some t
  | None => lookupTypViaIDFromInsnsC li' id0
  end
end.
    
Definition lookupTypViaIDFromBlockC (b:block) (id0:id) : option typ :=
match b with
| (block_intro _ li) => lookupTypViaIDFromInsnsC li id0
end.

Fixpoint lookupTypViaIDFromBlocksC (lb:list_block) (id0:id) : option typ :=
match lb with
| nil => None
| b::lb' =>
  match (lookupTypViaIDFromBlockC b id0) with
  | Some t => Some t
  | None => lookupTypViaIDFromBlocksC lb' id0
  end
end.

Definition lookupTypViaIDFromFdefC (fd:fdef) (id0:id) : option typ :=
match fd with
| (fdef_intro _ lb) => lookupTypViaIDFromBlocksC lb id0
end.

Definition lookupTypViaIDFromProductC (p:product) (id0:id) : option typ :=
match p with
| (product_function_dec _) => None
| (product_function_def fd) => lookupTypViaIDFromFdefC fd id0
end.

Fixpoint lookupTypViaIDFromProductsC (lp:list_product) (id0:id) : option typ :=
match lp with
| nil => None
| p::lp' =>
  match (lookupTypViaIDFromProductC p id0) with
  | Some t => Some t
  | None => lookupTypViaIDFromProductsC lp' id0
  end
end.

Definition lookupTypViaIDFromModuleC (m:module) (id0:id) : option typ :=
lookupTypViaIDFromProductsC m id0.
     
Fixpoint lookupTypViaIDFromModulesC (lm:list_module) (id0:id) : option typ :=
match lm with
| nil => None
| m::lm' =>
  match (lookupTypViaIDFromModuleC m id0) with
  | Some t => Some t
  | None => lookupTypViaIDFromModulesC lm' id0
  end
end.

Definition lookupTypViaIDFromSystemC (s:system) (id0:id) : option typ :=
lookupTypViaIDFromModulesC s id0.

(**********************************)
(* Eq. *)

Fixpoint typ_size (t:typ) : nat :=
  match t with
  | typ_int n => 1
  | typ_metadata => 1
  | typ_function t1 lt2 => 1+ typ_size t1 + fold_left plus (map typ_size lt2) 0
  | typ_void => 1
  | typ_label => 1
  | typ_array _ t' => 1 + typ_size t'
  | typ_pointer t' => 1 + typ_size t'
  end.

Definition typ2_size (txy:typ*typ) : nat :=
  let (tx, ty) := txy in
  typ_size tx + typ_size ty.

Lemma list_typ_size__inc : forall lt n n',
  n <= n' ->
  n <= fold_left plus (map typ_size lt) n'.
Proof.
  induction lt; intros; simpl; auto.
    apply IHlt; auto.
      omega.
Qed.

Lemma typ_size__ge__zero : forall t,
  typ_size t >= 0.
Proof.
  induction t as [ | | | | | t H l0 | ]; simpl; auto.
    assert (J:=@list_typ_size__inc l0 0 0).
    omega.
Qed.

Lemma list_typ_size__ge__typ_size : forall lt t n,
  In t lt ->
  typ_size t <= fold_left plus (map typ_size lt) n.
Proof.
  induction lt; intros; simpl.
    inversion H.

    simpl in H. inversion H.
      subst. apply list_typ_size__inc. omega.
      apply IHlt; auto.
Qed.

Lemma list_typ2_size__gt__typ2_size : forall t1 lt1 t1' lt1' t2 t2',
  In t2 lt1 ->
  In t2' lt1' ->
  typ2_size (t2, t2') < typ2_size (typ_function t1 lt1, typ_function t1' lt1').
Proof.
  intros.
  simpl.
  assert (J:=@list_typ_size__ge__typ_size lt1 t2 0 H).
  assert (J':=@list_typ_size__ge__typ_size lt1' t2' 0 H0).
  omega.
Qed. 

Definition create_elt tt t1 lt1 t1' lt1' t2 t2'
                (H1:In t2 lt1)
                (H2:In t2' lt1') 
                (H:(typ_function t1 lt1, typ_function t1' lt1') = tt):
  { t | typ2_size t < typ2_size tt }.
Proof.
  intros. subst.
  exists (t2, t2'). 
  apply list_typ2_size__gt__typ2_size; auto.
Qed.

Lemma head_in_incl : forall A (x:A) (l1' l1 l2:list A),
  l1 = x::l1'->
  incl l1 l2 ->
  In x l2.
Proof.
  intros A x l1' l1 l2 H1 H2.
  apply H2. subst. simpl. auto.
Qed.

Lemma prod_eq_inv : forall A (x y:A) (lt1' lt1 lt2' lt2:list A),
  (lt1, lt2) = (x::lt1', y::lt2') ->
  lt1 = x::lt1' /\ lt2 = y::lt2'.
Proof.
  intros A x y lt1' lt1 lt2' lt2 H.
  inversion H; subst. auto.
Qed.

Lemma tail_incl_incl : forall A (x:A) (l1' l1 l2:list A),
  l1 = x::l1'->
  incl l1 l2 ->
  incl l1' l2.
Proof.
  intros A x l1' l1 l2 H1 H2. subst.
  apply incl_tran with (m:=x::l1'); auto.
  assert ((x::nil)++l1'=x::l1') as Eq. simpl. auto.
  rewrite <- Eq.
  apply incl_appr; auto.
  apply incl_refl.
Qed.  

Fixpoint create_elts tt t1 lt1 t2 lt2 ltl ltr 
              (Hl:incl lt1 ltl) 
              (Hr:incl lt2 ltr)
              (H:(typ_function t1 ltl, typ_function t2 ltr) = tt ) 
              {struct lt1} :
  list {t: typ*typ | typ2_size t < typ2_size tt } := 
(match (lt1,lt2) as r return ((lt1, lt2) = r -> _) with
| (x::lt1', y::lt2') => 
  fun Ha:(lt1,lt2) = (x::lt1', y::lt2') =>
  match (prod_eq_inv typ x y lt1' lt1 lt2' lt2 Ha) with
  | conj Hal Har  =>
    (create_elt tt t1 ltl t2 ltr x y 
          (head_in_incl typ x lt1' lt1 ltl Hal Hl) 
          (head_in_incl typ y lt2' lt2 ltr Har Hr)  
          H)::
    (create_elts tt t1 lt1' t2 lt2' ltl ltr 
           (tail_incl_incl typ x lt1' lt1 ltl Hal Hl) 
           (tail_incl_incl typ y lt2' lt2 ltr Har Hr) 
           H)
  end
| (_, _) => 
  fun _ =>
  nil
end) (refl_equal (lt1, lt2)).

Definition combine_with_measure tt t1 lt1 t1' lt1' (H:(typ_function t1 lt1, typ_function t1' lt1') = tt ) :
  list {t: typ*typ | typ2_size t < typ2_size tt } := 
  create_elts tt t1 lt1 t1' lt1' lt1 lt1' (incl_refl lt1) (incl_refl lt1') H.

Program Fixpoint _typEqB (tt:typ*typ) {measure typ2_size} : bool :=
(match tt as r return (tt = r -> _) with 
| (typ_int n, typ_int n') => 
  fun _ =>
  match (eq_nat_dec n n') with
  | left _ => true 
  | right _ => false
  end 
| (typ_metadata, typ_metadata) => fun _ => true
| (typ_void, typ_void) => fun _ => true
| (typ_label, typ_label) => fun _ => true
| (typ_pointer t1, typ_pointer t1') => fun _ => _typEqB (t1, t1')
| (typ_array n t1, typ_array n' t1') => fun _ =>
  match (eq_nat_dec n n') with
  | left _ => _typEqB (t1, t1')
  | right _ => false
  end
| (typ_function t1 lt1, typ_function t1' lt1') =>
  fun Ha:(tt = (typ_function t1 lt1, typ_function t1' lt1')) =>
  match (eq_nat_dec (length lt1) (length lt1')) with
  | left _ => 
    _typEqB (t1, t1') &&
    fold_left andb (map _typEqB (combine_with_measure tt t1 lt1 t1' lt1' Ha)) true 
  | right _ => false
  end
| (_, _) => fun _ => false
end) (refl_equal tt).
Next Obligation.
  simpl. omega.
Qed.
Next Obligation.
  simpl. omega.
Qed.
Next Obligation.
  simpl. omega.
Qed.

Definition typEqB (t t':typ) : bool := _typEqB (t, t').

Definition constEqB (c c':const) : bool :=
match (c, c') with
| (const_val i, const_val i') => beq_nat i i'
| (const_undef, const_undec) => true
| (_, _) => false
end.

Definition valueEqB (v v':value) : bool :=
match (v, v') with
| (value_id i, value_id i') => beq_nat i i'
| (value_constant c, value_constant c') => constEqB c c'
| (_, _) => false
end.

Fixpoint _list_param_EqB (lp lp':list_param) {struct lp} : bool :=
match (lp, lp') with
| ((t,v)::lp0, (t',v')::lp0') =>
  typEqB t t' && valueEqB v v' &&
  _list_param_EqB lp0 lp0'
| (_, _) => true
end.

Definition list_param_EqB (lp lp':list_param) :=
  _list_param_EqB lp lp' && beq_nat (length lp) (length lp').

Fixpoint _id_labels_EqB (idls idls':id_labels) {struct idls} : bool :=
match (idls, idls') with
| ((id,l)::idls0, (id',l')::idls0') =>
  beq_nat id id' && beq_nat l l' &&
  _id_labels_EqB idls0 idls0'
| (_, _) => true
end.

Definition id_labels_EqB (idls idls':id_labels) :=
  _id_labels_EqB idls idls' && beq_nat (length idls) (length idls').

Definition insnEqB (i i':insn) : bool :=
match (i, i') with
| (insn_return t v, insn_return t' v') =>
  typEqB t t' && valueEqB v v'
| (insn_return_void, insn_return_void) => true
| (insn_br t v l1 l2, insn_br t' v' l1' l2') =>
  typEqB t t' && valueEqB v v' &&
  beq_nat l1 l1' && beq_nat l2 l2'
| (insn_br_uncond l, insn_br_uncond l') =>
  beq_nat l l'
| (insn_invoke id typ id0 paraml l1 l2,
   insn_invoke id' typ' id0' paraml' l1' l2') =>
  beq_nat id id' &&
  typEqB typ typ' &&
  beq_nat id0 id0' &&
  list_param_EqB paraml paraml' &&
  beq_nat l1 l1' &&
  beq_nat l2 l2'
| (insn_call id typ id0 paraml,
   insn_call id' typ' id0' paraml') =>
  beq_nat id id' &&
  typEqB typ typ' &&
  beq_nat id0 id0' &&
  list_param_EqB paraml paraml'
| (insn_unreachable, insn_unreachable) => true
| (insn_add id typ v1 v2,
   insn_add id' typ' v1' v2') =>
  beq_nat id id' &&
  typEqB typ typ' &&
  valueEqB v1 v1' &&
  valueEqB v2 v2'
| (insn_phi id typ idls,
   insn_phi id' typ' idls') =>
  beq_nat id id' &&
  typEqB typ typ' &&
  id_labels_EqB idls idls'
| (_, _) => false
end.

Definition blockEqB (b1 b2:block) : bool :=
match (eq_nat_dec (getBlockLabel b1) (getBlockLabel b2)) with
| left _ => true
| right _ => false
end.

Fixpoint _list_arg_EqB (la la':list_arg) {struct la} : bool :=
match (la, la') with
| ((t,id)::la0, (t',id')::la0') =>
  typEqB t t' && beq_nat id id' &&
  _list_arg_EqB la0 la0'
| (_, _) => true
end.

Definition list_arg_EqB (la la':list_arg) :=
  _list_arg_EqB la la' && beq_nat (length la) (length la').

Definition fheaderEqB (fh fh' : fheader) : bool :=
match (fh, fh') with
| (fheader_intro t id la, fheader_intro t' id' la') =>
  typEqB t t' && beq_nat id id' && list_arg_EqB la la'
end.

Fixpoint _blocksEqB (lb lb':list_block) {struct lb} : bool :=
match (lb, lb') with
| (b::lb0, b'::lb0') =>
  blockEqB b b' &&
  _blocksEqB lb0 lb0'
| (_, _) => true
end.

Definition blocksEqB (lb lb':list_block) :=
  _blocksEqB lb lb' && beq_nat (length lb) (length lb').

Definition fdecEqB (fd fd' : fdec) : bool :=
match (fd, fd') with
| (fdec_intro fh, fdec_intro fh') => fheaderEqB fh fh'
end.

Definition fdefEqB (fd fd' : fdef) : bool :=
match (fd, fd') with
| (fdef_intro fh lb, fdef_intro fh' lb') => 
  fheaderEqB fh fh' && blocksEqB lb lb'
end.

Definition productEqB (p p' : product) : bool :=
match (p, p') with
| (product_function_dec fd, product_function_dec fd') => fdecEqB fd fd'  
| (product_function_def fd, product_function_def fd') => fdefEqB fd fd'
| (_, _) => false
end.

Fixpoint _productsEqB (lp lp':list_product) {struct lp} : bool :=
match (lp, lp') with
| (p::lp0, p'::lp0') =>
  productEqB p p' &&
  _productsEqB lp0 lp0'
| (_, _) => true
end.

Definition productsEqB (lp lp':list_product) :=
  _productsEqB lp lp' && beq_nat (length lp) (length lp').

Definition moduleEqB (m m':module) := productsEqB m m'.

Fixpoint _modulesEqB (lm lm':list_module) {struct lm} : bool :=
match (lm, lm') with
| (m::lm0, m'::lm0') =>
  moduleEqB m m' &&
  _modulesEqB lm0 lm0'
| (_, _) => true
end.

Definition modulesEqB (lm lm':list_module) :=
  _modulesEqB lm lm' && beq_nat (length lm) (length lm').

Definition systemEqB (s s':system) := modulesEqB s s'.

(**********************************)
(* Inclusion. *)

Fixpoint InInsnsB (i:insn) (li:list_insn) {struct li} : bool :=
match li with
| nil => false
| i' :: li' => insnEqB i i' || InInsnsB i li'
end.

Definition insnInBlockB (i:insn) (b:block) : bool :=
match b with
| block_intro l insns => InInsnsB i insns
end.

Fixpoint InArgsB (a:arg) (la:list_arg) {struct la} : bool :=
match la with
| nil => false
| a' :: la' => 
  match (a, a') with
  | ((t, id), (t', id')) => typEqB t t' && beq_nat id id'
  end ||
  InArgsB a la'
end.

Definition argInFheaderB (a:arg) (fh:fheader) : bool :=
match fh with
| (fheader_intro t id la) => InArgsB a la
end.

Definition argInFdecB (a:arg) (fd:fdec) : bool :=
match fd with
| (fdec_intro fh) => argInFheaderB a fh
end.

Definition argInFdefB (a:arg) (fd:fdef) : bool :=
match fd with
| (fdef_intro fh lb) => argInFheaderB a fh
end.

Fixpoint InBlocksB (b:block) (lb:list_block) {struct lb} : bool :=
match lb with
| nil => false
| b' :: lb' => blockEqB b b' || InBlocksB b lb'
end.

Definition blockInFdefB (b:block) (fd:fdef) : bool :=
match fd with
| (fdef_intro fh lb) => InBlocksB b lb
end.

Fixpoint InProductsB (p:product) (lp:list_product) {struct lp} : bool :=
match lp with
| nil => false
| p' :: lp' => productEqB p p' || InProductsB p lp'
end.

Definition productInModuleB (p:product) (m:module) : bool :=
InProductsB p m.

Fixpoint InModulesB (m:module) (lm:list_module) {struct lm} : bool :=
match lm with
| nil => false
| m' :: lm' => moduleEqB m m' || InModulesB m lm'
end.

Definition moduleInSystemB (m:module) (s:system) : bool :=
InModulesB m s.

Definition productInSystemModuleB (p:product) (s:system) (mi:module_info) : bool :=
match mi with
| (m, (ui, ub)) =>
  moduleInSystemB m s && productInModuleB p m
end.

Definition blockInSystemModuleFdefB (b:block) (s:system) (mi:module_info) (fi:fdef_info) : bool :=
match fi with
| (fd, dt) =>
  blockInFdefB b fd && productInSystemModuleB (product_function_def fd) s mi
end.

Definition insnInSystemModuleFdefBlockB 
  (i:insn) (s:system) (mi:module_info) (fi:fdef_info) (b:block) : bool :=
insnInBlockB i b && blockInSystemModuleFdefB b s mi fi.

(**********************************)
(* parent *)

Fixpoint getParentOfInsnFromBlocksC (i:insn) (lb:list_block) {struct lb} : option block :=
match lb with
| nil => None
| b::lb' => 
  if (insnInBlockB i b) 
  then Some b
  else getParentOfInsnFromBlocksC i lb'
end.

Definition getParentOfInsnFromFdefC (i:insn) (fd:fdef) : option block :=
match fd with
| (fdef_intro _ lb) => getParentOfInsnFromBlocksC i lb
end.

Definition getParentOfInsnFromProductC (i:insn) (p:product) : option block :=
match p with
| (product_function_def fd) => getParentOfInsnFromFdefC i fd
| (product_function_dec _) => None
end.

Fixpoint getParentOfInsnFromProductsC (i:insn) (lp:list_product) {struct lp} : option block :=
match lp with
| nil => None
| p::lp' =>
  match (getParentOfInsnFromProductC i p) with
  | Some b => Some b
  | None => getParentOfInsnFromProductsC i lp'
  end
end.

Definition getParentOfInsnFromModuleC (i:insn) (m:module) : option block := 
  getParentOfInsnFromProductsC i m.

Fixpoint getParentOfInsnFromModulesC (i:insn) (lm:list_module) {struct lm} : option block :=
match lm with
| nil => None
| m::lm' =>
  match (getParentOfInsnFromModuleC i m) with
  | Some b => Some b
  | None => getParentOfInsnFromModulesC i lm'
  end
end.

Definition getParentOfInsnFromSystemC (i:insn) (s:system) : option block := 
  getParentOfInsnFromModulesC i s.

Definition insnHasParent (i:insn) (s:system) : bool :=
match (getParentOfInsnFromSystemC i s) with
| Some _ => true
| None => false
end.

Fixpoint getParentOfFdefFromModulesC (fd:fdef) (lm:list_module) {struct lm} : option module :=
match lm with
| nil => None
| m::lm' => 
  if (productInModuleB (product_function_def fd) m) 
  then Some m
  else getParentOfFdefFromModulesC fd lm'
end.

Definition getParentOfFdefFromSystemC (fd:fdef) (s:system) : option module := 
  getParentOfFdefFromModulesC fd s.

Notation "t =t= t' " := (typEqB t t') (at level 50).
Notation "n =n= n'" := (beq_nat n n') (at level 50).
Notation "b =b= b'" := (blockEqB b b') (at level 50).
Notation "i =i= i'" := (insnEqB i i') (at level 50).

(*ENDCOPY*)

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "./ott" "-I" "./monads") ***
*** End: ***
 *)


