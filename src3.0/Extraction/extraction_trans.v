Require Import extraction_core.
Require Import dom_tree.
Require Import dom_set_tree.
Require Import dom_list.
Require Import primitives.
Require Import gvn.
Require Import vmem2reg.
Require Import vmem2reg_opt.
Require Import vmem2reg_opt2.

Extract Constant print_reachablity => "Transforms_aux.print_reachablity".
Extract Constant print_dominators => "Transforms_aux.print_dominators".
Extract Constant print_adtree => "Transforms_aux.print_dtree (fun a -> a) ".
Extract Constant TNAME => "int".
Extract Constant init_expected_name => "Transforms_aux.init_expected_name".
Extract Constant check_bname => "Transforms_aux.check_bname".
Extract Constant check_vname => "Transforms_aux.check_vname".
Extract Constant does_pre => "Transforms_aux.does_pre".
Extract Constant does_load_elim => "Transforms_aux.does_load_elim".
Extract Constant does_phi_elim => "Transforms_aux.does_phi_elim".
(*Extract Constant does_macro_m2r => "Transforms_aux.does_macro_m2r".*)
Extract Constant does_stld_elim => "Transforms_aux.does_stld_elim".
Extract Constant does_dead_phi_elim => "Transforms_aux.does_dead_phi_elim".
Extract Constant is_llvm_dbg_declare => "Transforms_aux.is_llvm_dbg_declare".
Extract Constant is_llvm_lifetime => "Transforms_aux.is_llvm_lifetime".

Extract Constant open_aa_db => "Transforms_aux.open_aa_db".
Extract Constant read_aa_from_fun => "Transforms_aux.read_aa_from_fun".
Extract Constant is_no_alias_id => "Transforms_aux.is_no_alias".
Extract Constant is_must_alias_id => "Transforms_aux.is_must_alias".

Extraction Library dom_tree.
Extraction Library dom_set_tree.
Extraction Library dom_list.
Extraction Library primitives.
Extraction Library gvn.
Extraction Library iter_pass.
Extraction Library pass_combinators.
Extraction Library vmem2reg.
Extraction Library vmem2reg_opt.
Extraction Library vmem2reg_opt2.
