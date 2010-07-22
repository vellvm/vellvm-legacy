Add LoadPath "../ssa/ott".
Add LoadPath "../ssa/monads".
Add LoadPath "../ssa".
Add LoadPath "../../theory/metatheory".
Require Import ssa.
Require Import List.
Require Export targetdata.
Require Import monad.
Require Import Arith.

(** symbolic terms, values and memories. *)
Inductive sterm : Set := 
| sterm_val : value -> sterm
| sterm_bop : bop -> sz -> sterm -> sterm -> sterm
| sterm_extractvalue : typ -> sterm -> list const -> sterm
| sterm_insertvalue : typ -> sterm -> typ -> sterm -> list const -> sterm
| sterm_malloc : smem -> typ -> sz -> align -> sterm
| sterm_alloca : smem -> typ -> sz -> align -> sterm
| sterm_load : smem -> typ -> sterm -> sterm
| sterm_gep : inbounds -> typ -> sterm -> list sterm -> sterm
| sterm_ext : extop -> typ -> sterm -> typ -> sterm
| sterm_cast : castop -> typ -> sterm -> typ -> sterm
| sterm_icmp : cond -> typ -> sterm -> sterm -> sterm
| sterm_phi : typ -> list (sterm*l) -> sterm
| sterm_select : sterm -> typ -> sterm -> sterm -> sterm
| sterm_call : tailc -> typ -> id -> list (typ*sterm) -> sterm
with smem : Set :=
| smem_init : smem
| smem_malloc : smem -> typ -> sz -> align -> smem
| smem_free : smem -> typ -> sterm -> smem
| smem_alloca : smem -> typ -> sz -> align -> smem
| smem_load : smem -> typ -> sterm -> smem
| smem_store : smem -> typ -> sterm -> sterm -> smem
.

Definition smap := id -> option sterm.
Definition effects := list sterm.

Record sstate : Set := mkSstate 
{
  STerms : smap;
  SMem : smem;
  Effects : effects
}.

Definition updateSmap (STerms:smap) (id0:id) (s:sterm) : smap :=
fun (id1:id) => if beq_nat id0 id1 then Some s else STerms id1.

Fixpoint subst_sterm (id0:id) (s0:sterm) (s:sterm) : sterm :=
match s with
| sterm_val (value_id id1) => if beq_nat id0 id1 then s0 else s
| sterm_val (value_const c) => sterm_val (value_const c)
| sterm_bop op sz s1 s2 => 
    sterm_bop op sz (subst_sterm id0 s0 s1) (subst_sterm id0 s0 s2)
| sterm_extractvalue t1 s1 cs => 
    sterm_extractvalue t1 (subst_sterm id0 s0 s1) cs
| sterm_insertvalue t1 s1 t2 s2 cs => 
    sterm_insertvalue t1 (subst_sterm id0 s0 s1) t2 (subst_sterm id0 s0 s2) cs
| sterm_malloc m1 t1 sz align => 
    sterm_malloc (subst_smem id0 s0 m1) t1 sz align
| sterm_alloca m1 t1 sz align => 
    sterm_alloca (subst_smem id0 s0 m1) t1 sz align
| sterm_load m1 t1 s1 => 
    sterm_load (subst_smem id0 s0 m1) t1 (subst_sterm id0 s0 s1)
| sterm_gep inbounds t1 s1 ls2 =>
    sterm_gep inbounds t1 (subst_sterm id0 s0 s1) (map (subst_sterm id0 s0) ls2)
| sterm_ext extop t1 s1 t2 => 
    sterm_ext extop t1 (subst_sterm id0 s0 s1) t2
| sterm_cast castop t1 s1 t2 => 
    sterm_cast castop t1 (subst_sterm id0 s0 s1) t2
| sterm_icmp cond t1 s1 s2 => 
    sterm_icmp cond t1 (subst_sterm id0 s0 s1) (subst_sterm id0 s0 s2)
| sterm_phi t1 lsl1 => 
    sterm_phi t1 (map 
                   (fun (sl1:sterm*l) => 
                    let (s1,l1):=sl1 in 
                    ((subst_sterm id0 s0 s1), l1)
                   ) 
                   lsl1)
| sterm_select s1 t1 s2 s3 => 
    sterm_select (subst_sterm id0 s0 s1) t1 (subst_sterm id0 s0 s2) (subst_sterm id0 s0 s3)
| sterm_call tailc t1 id1 lts1 => 
    sterm_call tailc t1 id1 
                 (map 
                   (fun (ts1:typ*sterm) => 
                    let (t1,s1):=ts1 in 
                    (t1, (subst_sterm id0 s0 s1))
                   ) 
                   lts1)
end
with subst_smem (id0:id) (s0:sterm) (m:smem) : smem :=
match m with 
| smem_init => smem_init
| smem_malloc m1 t1 sz align => smem_malloc (subst_smem id0 s0 m1) t1 sz align
| smem_free m1 t1 s1 => smem_free (subst_smem id0 s0 m1) t1 (subst_sterm id0 s0 s1)
| smem_alloca m1 t1 sz align => smem_alloca (subst_smem id0 s0 m1) t1 sz align
| smem_load m1 t1 s1 => smem_load (subst_smem id0 s0 m1) t1 (subst_sterm id0 s0 s1)
| smem_store m1 t1 s1 s2 => smem_store (subst_smem id0 s0 m1) t1 (subst_sterm id0 s0 s1) (subst_sterm id0 s0 s2)
end
.

Fixpont subst_

Definition se_insn (st : sstate) (i:insn) : option sstate :=
match i with 
| insn_bop id0 op0 sz0 v1 v2 => 
  Some (mkSstate (updateSValue st.(SValues) id0 
                   (sterm_bop op0 sz0 (svalue_val v1) (svalue_val v2)))
                 st.(SMem)
                 st.(Effects))
| insn_extractvalue id0 t1 v1 cs3 =>
  Some (mkSstate (updateSValue st.(SValues) id0 
                   (sterm_extractvalue t1 (svalue_val v1) cs3))
                 st.(SMem) 
                 st.(Effects))
| insn_insertvalue id0 t1 v1 t2 v2 cs3 =>  
  Some (mkSstate (updateSValue st.(SValues) id0 
                   (sterm_insertvalue t1 (svalue_val v1) t2 (svalue_val v2) cs3))
                 st.(SMem) 
                 st.(Effects))
| insn_malloc id0 t1 sz1 al1 =>  
  Some (mkSstate (updateSValue st.(SValues) id0 
                   (sterm_malloc st.(SMem) t1 sz1 al1))
                 (smem_malloc st.(SMem) t1 sz1 al1)
                 st.(Effects))
| insn_free t0 v0 =>  
  Some (mkSstate st.(SValues)
                (smem_free st.(SMem) t0 (svalue_val v0))
                 st.(Effects))
| insn_alloca id0 t1 sz1 al1 =>  
  Some (mkSstate (updateSValue st.(SValues) id0 
                   (sterm_alloca st.(SMem) t1 sz1 al1))
                 (smem_alloca st.(SMem) t1 sz1 al1)
                 st.(Effects))
| insn_load id0 t2 v2 =>  
  Some (mkSstate (updateSValue st.(SValues) id0 
                   (sterm_load st.(SMem) t2 (svalue_val v2)))
                 (smem_load st.(SMem) t2 (svalue_val v2))
                 st.(Effects))
| insn_store t0 v1 v2 =>  
  Some (mkSstate st.(SValues)
                 (smem_store st.(SMem) t0 (svalue_val v1) (svalue_val v2))
                 st.(Effects))
| insn_gep id0 inbounds0 t1 v1 lv2 =>  
  Some (mkSstate (updateSValue st.(SValues) id0 
                   (sterm_gep inbounds0 t1 (svalue_val v1) (map svalue_val lv2)))
                 st.(SMem) 
                 st.(Effects))
| insn_ext id0 op0 t1 v1 t2 =>  
  Some (mkSstate (updateSValue st.(SValues) id0 
                   (sterm_ext op0 t1 (svalue_val v1) t2))
                 st.(SMem) 
                 st.(Effects))
| insn_cast id0 op0 t1 v1 t2 =>  
  Some (mkSstate (updateSValue st.(SValues) id0 
                   (sterm_cast op0 t1 (svalue_val v1) t2))
                 st.(SMem) 
                 st.(Effects))
| insn_icmp id0 c0 t0 v1 v2 =>  
  Some (mkSstate (updateSValue st.(SValues) id0 
                   (sterm_icmp c0 t0 (svalue_val v1) (svalue_val v2)))
                 st.(SMem) 
                 st.(Effects))
| insn_phi id0 t0 idls0 =>  
  Some (mkSstate (updateSValue st.(SValues) id0 
                   (sterm_phi t0 idls0))
                 st.(SMem) 
                 st.(Effects))
| insn_select id0 v0 t0 v1 v2 =>  
  Some (mkSstate (updateSValue st.(SValues) id0 
                   (sterm_select (svalue_val v0) t0 (svalue_val v1) (svalue_val v2)))
                 st.(SMem) 
                 st.(Effects))
| insn_call (Some id0) tailc0 t1 id1 list_param1 =>  
  Some (mkSstate (updateSValue st.(SValues) id0 
                   (sterm_call tailc0 t1 id1 list_param1))
                 st.(SMem) 
                 st.(Effects))
| insn_call None tailc0 t1 id1 list_param1 =>  
  Some (mkSstate st.(SValues)
                 st.(SMem) 
                 ((sterm_call tailc0 t1 id1 list_param1)::st.(Effects)))
| _ => None 
end.


