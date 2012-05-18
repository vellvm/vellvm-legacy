Require Import List.
Require Import ListSet.
Require Import Coqlib.
Require Import Metatheory.
Require Import Maps.
Require Import Lattice.
Require Import Kildall.
Require Import Iteration.
Require Import cfg.
Require Import reach.
Require Import Dipaths.

Require Import syntax.
Require Import infrastructure.
Require Import infrastructure_props.
Import LLVMsyntax.
Import LLVMinfra.

Module Type ALGDOM.

Parameter dom_analysis_is_successful : fdef -> Prop.

Parameter dom_query : fdef -> atom -> set atom.

Axiom dom_entrypoint : forall f l0 ps cs tmn
  (Hentry : getEntryBlock f = Some (block_intro l0 ps cs tmn)),
  dom_query f l0 = nil.

Axiom entry_doms_others: forall (f:fdef) entry
  (Hex: dom_analysis_is_successful f)
  (H: getEntryLabel f = Some entry),
  (forall b (H0: b <> entry /\ reachable f b),
     ListSet.set_In entry (dom_query f b)).

Axiom dom_query_in_bound: forall fh bs l5, 
  incl (dom_query (fdef_intro fh bs) l5) (bound_blocks bs).

Axiom dom_successors : forall
  (l3 : l) (l' : l) f
  (contents3 contents': ListSet.set atom)
  (Hinscs : In l' (successors f) !!! l3)
  (Heqdefs3 : contents3 = dom_query f l3)
  (Heqdefs' : contents' = dom_query f l'),
  incl contents' (l3 :: contents3).

Axiom sdom_is_complete: forall (f:fdef)
  (branches_in_vertexes: forall p ps0 cs0 tmn0 l2
    (J3 : blockInFdefB (block_intro p ps0 cs0 tmn0) f)
    (J4 : In l2 (successors_terminator tmn0)),
    vertexes_fdef f (index l2))
  (l3 : l) (l' : l) ps cs tmn ps' cs' tmn'
  (HuniqF : uniqFdef f)
  (Hsucc: dom_analysis_is_successful f)
  (HBinF' : blockInFdefB (block_intro l' ps' cs' tmn') f = true)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hsdom: strict_domination f l' l3),
  In l' (dom_query f l3).

Axiom dom_unreachable: forall (f:fdef)
  (branches_in_vertexes: forall p ps0 cs0 tmn0 l2
    (J3 : blockInFdefB (block_intro p ps0 cs0 tmn0) f)
    (J4 : In l2 (successors_terminator tmn0)),
    vertexes_fdef f (index l2))
  (Hhasentry: getEntryBlock f <> None)
  (l3 : l) (l' : l) ps cs tmn
  (Hsucc: dom_analysis_is_successful f)
  (HuniqF: uniqFdef f)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hunreach: ~ reachable f l3),
  dom_query f l3 = bound_fdef f.

Axiom dom_is_sound : forall (f : fdef)
  (Hhasentry: getEntryBlock f <> None)
  (l3 : l) (l' : l) ps cs tmn
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hin : In l' (l3::(dom_query f l3))),
  domination f l' l3.

Axiom sdom_is_sound : forall (f : fdef)
  (Hhasentry: getEntryBlock f <> None)
  (l3 : l) (l' : l) ps cs tmn
  (Hreach : reachable f l3)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hin : In l' (dom_query f l3)),
  strict_domination f l' l3.

Axiom sdom_isnt_refl : forall (f : fdef)
  (Hhasentry: getEntryBlock f <> None)
  (l3 : l) (l' : l) ps cs tmn
  (Hreach : reachable f l3)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hin : In l' (dom_query f l3)),
  l' <> l3.

Definition getEntryBlock_inv f := forall
  (l3 : l) (l' : l)
  (ps : phinodes)
  (cs : cmds)
  (tmn : terminator)
  (HBinF : blockInFdefB (block_intro l3 ps cs tmn) f = true)
  (Hsucc : In l' (successors_terminator tmn)) a ps0 cs0 tmn0
  (H : getEntryBlock f = Some (block_intro a ps0 cs0 tmn0)),
  l' <> a.

Axiom adom_acyclic: forall f 
  (Hhasentry: getEntryBlock f <> None)
  (HgetEntryBlock_inv : getEntryBlock_inv f)
  l1 l2 ps1 cs1 tmn1 ps2 cs2 tmn2,
  reachable f l2 ->
  blockInFdefB (block_intro l1 ps1 cs1 tmn1) f = true ->
  blockInFdefB (block_intro l2 ps2 cs2 tmn2) f = true ->
  In l1 (dom_query f l2) ->
  In l2 (dom_query f l1) ->
  l1 <> l2 ->
  False.

Axiom pres_dom_query: forall 
  (ftrans: fdef -> fdef) 
  (btrans: block -> block)
  (ftrans_spec: forall fh bs, 
    ftrans (fdef_intro fh bs) = fdef_intro fh (List.map btrans bs))
  (btrans_eq_label: forall b, getBlockLabel b = getBlockLabel (btrans b))
  (btrans_eq_tmn: forall b, 
    terminator_match (getBlockTmn b) (getBlockTmn (btrans b)))
  (f : fdef) (l5 l0 : l),
  ListSet.set_In l5 (dom_query f l0) <->
  ListSet.set_In l5 (dom_query (ftrans f) l0).

Axiom pres_dom_analysis_is_successful : forall 
  (ftrans: fdef -> fdef) 
  (btrans: block -> block)
  (ftrans_spec: forall fh bs, 
    ftrans (fdef_intro fh bs) = fdef_intro fh (List.map btrans bs))
  (btrans_eq_label: forall b, getBlockLabel b = getBlockLabel (btrans b))
  (btrans_eq_tmn: forall b, 
    terminator_match (getBlockTmn b) (getBlockTmn (btrans b))) f,
  dom_analysis_is_successful f <-> 
    dom_analysis_is_successful (ftrans f).

End ALGDOM.

