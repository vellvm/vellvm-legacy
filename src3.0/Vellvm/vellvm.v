Require Export alist.
Require Export Integers.
Require Export Values.
Require Export Coqlib.
Require Export monad.
Require Export events.
Require Export Memory.
Require Export Metatheory.
Require Export Znumtheory.
Require Import syntax.
Require Import infrastructure.
Require Export analysis.
Require Import typings.
Require Import genericvalues.
Require Import targetdata.
Require Export infrastructure_props.
Require Export static.
Require Export opsem.
Require Export opsem_wf.
Require Export dopsem.
Require Export ndopsem.
Require Export external_intrinsics.
Require Export vellvm_tactics.

Export LLVMsyntax.
Export LLVMinfra.
Export LLVMgv.
Export LLVMtd.
Export LLVMtypings.

Ltac destruct_cmd cmd :=
let i0 := fresh "i0" in
let i1 := fresh "i1" in
let b := fresh "b" in
let s0 := fresh "s0" in
let v := fresh "v" in
let v0 := fresh "v0" in
let v1 := fresh "v1" in
let f0 := fresh "f0" in
let f1 := fresh "f1" in
let t := fresh "t" in
let t0 := fresh "t0" in
let t1 := fresh "t1" in
let l2 := fresh "l2" in
let a := fresh "a" in
let p := fresh "p" in
let n := fresh "n" in
let c := fresh "c" in
let e := fresh "e" in
destruct cmd as [i0 b s0 v v0|i0 f0 f1 v v0|i0 t v l2|i0 t v t0 v0 l2|
                 i0 t v a|i0 t v|i0 t v a|i0 t v a|i0 t v v0 a|i0 i1 t v l2|
                 i0 t t0 v t1|i0 e t v t0|i0 c t v t0|i0 c t v v0|
                 i0 f0 f1 v v0|i0 v t v0 v1|i0 n c t v p].

Ltac destruct_typ t :=
let s0 := fresh "s0" in
let f := fresh "f" in
let t0 := fresh "t0" in
let lt0 := fresh "lt0" in
let i0 := fresh "i0" in
destruct t as [s0 | f | | | | s0 t0 | t0 lt0 | lt0 | t0 | i0 ].

Ltac destruct_const cst :=
let Int5 := fresh "Int5" in
let i0 := fresh "i0" in
let b := fresh "b" in
let sz5 := fresh "sz5" in
let f0 := fresh "f0" in
let f1 := fresh "f1" in
let t := fresh "t" in
let t0 := fresh "t0" in
let l2 := fresh "l2" in
let c0 := fresh "c0" in
let c1 := fresh "c1" in
let c2 := fresh "c2" in
let e := fresh "e" in
let cs0 := fresh "cs0" in
destruct cst as [t|sz5 Int5|f0 f1|t|t|t cs0|t cs0|t i0|t c0 t0|e c0 t0|c0 c1 t0|
                 i0 c0 cs0|c0 c1 c2|c0 c1 c2|f0 c1 c2|c0 cs0|c0 c1 cs0|
                 b c0 c1|f0 c0 c1].

Ltac destruct_tmn tmn :=
let id5 := fresh "id5" in
let t := fresh "t" in
let value5 := fresh "value5" in
let l2 := fresh "l2" in
let l3 := fresh "l3" in
let i0 := fresh "i0" in
destruct tmn as [id5 t value5 | id5 | id5 value5 l2 l3 | i0 l2 | ].

Ltac repeat_bsplit :=
  repeat (bsplit; auto using eq_sumbool2bool_true).

