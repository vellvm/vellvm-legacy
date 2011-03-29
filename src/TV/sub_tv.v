Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa".
Add LoadPath "../ssa/compcert".
Add LoadPath "../../../theory/metatheory_8.3".
Require Import ssa_def.
Require Import ssa_lib.
Require Import List.
Require Import targetdata.
Require Import monad.
Require Import Arith.
Require Import Metatheory.
Require Import ssa_mem.
Require Import genericvalues.
Require Import ssa_dynamic.
Require Import opsem_pp.
Require Import trace.
Require Import symexe_def.
Require Import symexe_lib.
Require Import symexe_complete.
Require Import symexe_sound.
Require Import seop_llvmop.
Require Import assoclist.
Require Import ssa_props.
Require Import eq_tv_dec.
Require Import sub_tv_dec.
Require Import Coq.Bool.Sumbool.

Export SimpleSE.

Definition tv_cmds (nbs1 nbs2 : list nbranch) :=
sumbool2bool _ _ (sstate_sub_dec (se_cmds sstate_init nbs1) (se_cmds sstate_init nbs2)
                    (se_cmds_init_uniq nbs1)).

(* Realized to check if two function names are matched. For example,
 * in Softbound, 'test' in the original program matches 'softbound_test'.
*)
Axiom tv_fid : id -> id -> bool.

Axiom tv_fid_injective1 : forall fid1 fid2 fid1' fid2',
  fid1 = fid2 -> tv_fid fid1 fid1' -> tv_fid fid2 fid2' -> fid1' = fid2'.

Axiom tv_fid_injective2 : forall fid1 fid2 fid1' fid2',
  fid1 <> fid2 -> tv_fid fid1 fid1' -> tv_fid fid2 fid2' -> fid1' <> fid2'.

(* Here, we check which function to call conservatively. In practice, a v1
 * is a function pointer, we should look up the function name from the 
 * FunTable. Since the LLVM IR takes function names as function pointers,
 * if a program does not assign them to be other variables, they should
 * be the same. *)
Definition tv_scall (c1 c2:scall) :=
  let '(stmn_call rid1 nr1 tailc1 t1 v1 sts1) := c1 in
  let '(stmn_call rid2 nr2 tailc2 t2 v2 sts2) := c2 in
  (sumbool2bool _ _ (id_dec rid1 rid1)) &&
  (sumbool2bool _ _ (noret_dec nr1 nr2)) &&
  (sumbool2bool _ _ (tailc_dec tailc1 tailc2)) &&
  (sumbool2bool _ _ (typ_dec t1 t2)) && 
  (sumbool2bool _ _ (prefix_dec _ typ_sterm_dec sts1 sts2)) &&
  match (v1, v2) with
  | (value_const (const_gid _ fid1), value_const (const_gid _ fid2)) => 
      tv_fid fid1 fid2
  | (v1, v2) => sumbool2bool _ _ (value_dec v1 v2)
  end.

Definition tv_subblock (sb1 sb2:subblock) :=
match (sb1, sb2) with
| (mkSB nbs1 call1 iscall1, mkSB nbs2 call2 iscall2) =>
  let st1 := se_cmds sstate_init nbs1 in
  let st2 := se_cmds sstate_init nbs2 in
  let cl1 := se_call st1 call1 iscall1 in
  let cl2 := se_call st2 call2 iscall2 in
   (sumbool2bool _ _ (sstate_sub_dec st1 st2 (se_cmds_init_uniq nbs1))) &&
   tv_scall cl1 cl2
end.

Fixpoint tv_subblocks (sbs1 sbs2:list subblock) :=
match (sbs1, sbs2) with
| (nil, nil) => true
| (sb1::sbs1', sb2::sbs2') => 
   (tv_subblock sb1 sb2) && (tv_subblocks sbs1' sbs2')
| _ => false
end.

Fixpoint tv_phinodes (ps1 ps2:phinodes) :=
match (ps1, ps2) with
| (nil, nil) => true
| (p1::ps1', p2::ps2') => 
    sumbool2bool _ _ (phinode_dec p1 p2) && tv_phinodes ps1' ps2'
| _ => false
end.

Definition tv_block (b1 b2:block) :=
match (b1, b2) with
| (block_intro l1 ps1 cs1 tmn1, block_intro l2 ps2 cs2 tmn2) =>
  match (cmds2sbs cs1, cmds2sbs cs2) with
  | ((sbs1, nbs1), (sbs2, nbs2)) =>
    sumbool2bool _ _ (eq_atom_dec l1 l2) &&
    tv_phinodes ps1 ps2 &&
    tv_subblocks sbs1 sbs2 &&
    tv_cmds nbs1 nbs2 &&
    sumbool2bool _ _ (terminator_dec tmn1 tmn2)
  end
end.

Fixpoint tv_blocks (bs1 bs2:blocks):=
match (bs1, bs2) with
| (nil, nil) => true
| (b1::bs1', b2::bs2') => tv_block b1 b2 && tv_blocks bs1' bs2'
| _ => false
end.

Definition tv_fheader (f1 f2:fheader) := 
  let '(fheader_intro t1 fid1 a1) := f1 in
  let '(fheader_intro t2 fid2 a2) := f2 in
  (sumbool2bool _ _ (typ_dec t1 t2)) &&
  tv_fid fid1 fid2 &&
  (sumbool2bool _ _ (prefix_dec _ arg_dec a1 a2)).

Definition tv_fdef (f1 f2:fdef) :=
match (f1, f2) with
| (fdef_intro fh1 lb1, fdef_intro fh2 lb2) =>
  tv_fheader fh1 fh2 && tv_blocks lb1 lb2
end.

Fixpoint tv_products (Ps1 Ps2:products):=
match (Ps1, Ps2) with
| (nil, nil) => true
| (product_fdec f1::Ps1', product_fdec f2::Ps2') => 
  sumbool2bool _ _ (fdec_dec f1 f2) &&
  tv_products Ps1' Ps2'
| (product_fdef f1::Ps1', product_fdef f2::Ps2') => 
  tv_fdef f1 f2 && tv_products Ps1' Ps2'
| (product_gvar gvar1::Ps1', product_gvar gvar2::Ps2') => 
  sumbool2bool _ _ (gvar_dec gvar1 gvar2) &&
  tv_products Ps1' Ps2'
| _ => false
end.

Definition tv_module (m1 m2:module) :=
match (m1, m2) with
| (module_intro los1 nts1 Ps1, module_intro los2 nts2 Ps2) =>
  sumbool2bool _ _ (layouts_dec los1 los2) &&
  sumbool2bool _ _ (namedts_dec nts1 nts2) &&
  tv_products Ps1 Ps2
end.

Fixpoint tv_system (S1 S2:system) :=
match (S1, S2) with
| (nil, nil) => true
| (m1::S1', m2::S2') => tv_module m1 m2 && tv_system S1' S2'
| _ => false
end.

Ltac sumbool_simpl :=
  repeat
  match goal with
  | [ H:sumbool2bool _ _ _ = true |- _ ] => apply sumbool2bool_true in H
  | [ H:is_true(sumbool2bool _ _ _) |- _ ] => apply sumbool2bool_true in H
  | [ H:tv_cmds _ _ = true |- _ ] => unfold is_true in H; apply sumbool2bool_true in H
  | [ H:is_true(tv_cmds _ _) |- _ ] => unfold is_true in H; apply sumbool2bool_true in H
  end.

(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)
