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
Require Import ZArith.
Require Import Metatheory.
Require Import Memory.
Require Import Values.
Require Import ssa_mem.
Require Import trace.
Require Import symexe_def.
Require Import assoclist.
Require Import ssa_props.
Require Import sub_tv_dec.
Require Import sub_tv_infer.
Require Import sub_tv.
Require Import Coq.Bool.Sumbool.
Require Import symexe_tactic.

Definition ptr_has_basebound TD M vb ve vp : bool :=
match (GV2ptr TD (getPointerSize TD) vb, 
       GV2ptr TD (getPointerSize TD) ve,
       GV2ptr TD (getPointerSize TD) vp) with
| (Some (Vptr bb ob), Some (Vptr be oe), Some (Vptr bp op)) =>
  let '(lo,hi) := Memory.Mem.bounds M bp in
  bzeq bb be && bzeq bb bp && 
  bzeq (Integers.Int.unsigned 31 ob) lo && 
  bzeq (Integers.Int.unsigned 31 oe) hi           
| _ => false
end.

(* fs: function table
 * lc: local variable mappings
*)
Fixpoint valid_metadata (TD:TargetData) (fs lc:GVMap) (M:mem) (md:metadata) 
  : bool :=
match md with
| nil => true
| (fid,lbl,nth,b,e,p,true)::md' =>
    match (lookupAL _ lc b, lookupAL _ lc e, lookupAL _ lc p) with
    | (Some vb, Some ve, Some vp) => ptr_has_basebound TD M vb ve vp
    | (None, None, None) => true
    | _ => false
    end && valid_metadata TD fs lc M md'
| (fid,lbl,nth,b,e,p,false)::md' => 
    match (lookupAL _ lc b, lookupAL _ lc e, lookupAL _ lc p) with
    | (Some vb, Some ve, Some vp) => 
        match (lookupFdefViaGVFromFunTable fs vb,
               lookupFdefViaGVFromFunTable fs ve,
               lookupFdefViaGVFromFunTable fs vp) with
        | (Some fid1, Some fid2, Some fid3) => eq_id fid1 fid2 && eq_id fid3 fid3
        | _ => false
        end        
    | (None, None, None) => true
    | _ => false
    end && valid_metadata TD fs lc M md'
end.

Definition valid_memdata_db (TD:TargetData) (M:mem) := 
  forall addrofp t p vaddrofb vaddrofe ps lc gl oresult M' vb ve vp fid
    addrofb addrofe,
  mload TD M addrofp (typ_pointer t) Align.One = Some vp ->
  is_hashLoadBaseBound fid = true ->
  callLib M fid (params2GVs TD 
    (p::
     (typ_pointer (typ_pointer (typ_int Size.Eight)),vaddrofb)::
     (typ_pointer (typ_pointer (typ_int Size.Eight)),vaddrofe)::
     ps) lc gl) = 
    Some (oresult, M') ->
  getOperandValue TD vaddrofb lc gl = Some addrofb ->
  getOperandValue TD vaddrofe lc gl = Some addrofe ->
  mload TD M' addrofb (typ_pointer (typ_int Size.Eight)) Align.One = Some vb ->
  mload TD M' addrofe (typ_pointer (typ_int Size.Eight)) Align.One = Some ve ->
  ptr_has_basebound TD M vb ve vp = true.

  


(*****************************)
(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "~/SVN/sol/vol/src/ssa/monads" "-I" "~/SVN/sol/vol/src/ssa/ott" "-I" "~/SVN/sol/vol/src/ssa/compcert" "-I" "~/SVN/sol/theory/metatheory_8.3") ***
*** End: ***
 *)




