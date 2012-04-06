Require Import vellvm.
Require Import Kildall.
Require Import ListSet.
Require Import Maps.
Require Import Lattice.
Require Import Iteration.
Require Import dtree.
Require Import primitives.
Require Import mem2reg.
Require Import opsem_props.
Require Import palloca_props.
Require Import program_sim.

Lemma phinodes_placement_wfS: forall rd f Ps1 Ps2 los nts pid ty al
  num l0 ps0 cs0 tmn0 dones (Hreach: ret rd = dtree.reachablity_analysis f)
  (Hentry: getEntryBlock f = Some (block_intro l0 ps0 cs0 tmn0))
  (Hfind: find_promotable_alloca f cs0 dones = Some (pid, ty, num, al))
  (HwfS :
     wf_system 
       [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]),
  wf_system 
    [module_intro los nts
      (Ps1 ++
       product_fdef (phinodes_placement f rd pid ty al (successors f)
                    (make_predecessors (successors f))) :: Ps2)].
Admitted. (* WF prev *)

Lemma phinodes_placement_wfPI: forall rd f Ps1 Ps2 los nts pid ty al
  num l0 ps0 cs0 tmn0 dones (Hreach: ret rd = dtree.reachablity_analysis f)
  (Hentry: getEntryBlock f = Some (block_intro l0 ps0 cs0 tmn0))
  (Hfind: find_promotable_alloca f cs0 dones = Some (pid, ty, num, al))
  (HwfS :
     wf_system 
       [module_intro los nts (Ps1 ++ product_fdef f :: Ps2)]),
  WF_PhiInfo {|
    PI_f := phinodes_placement f rd pid ty al (successors f)
              (make_predecessors (successors f));
    PI_rd := rd;
    PI_id := pid;
    PI_typ := ty;
    PI_num := num;
    PI_align := al |}.
Admitted. (* WF prev *)

Lemma phinodes_placement_reachablity_analysis: forall f rd pid ty al,
  dtree.reachablity_analysis f =
  dtree.reachablity_analysis
     (phinodes_placement f rd pid ty al (successors f)
        (make_predecessors (successors f))).
Admitted. (* WF prev *)

Lemma phinodes_placement_reachablity_successors: forall f rd pid ty al,
  successors f =
  successors
    (phinodes_placement f rd pid ty al (successors f)
       (make_predecessors (successors f))).
Admitted. (* WF prev *)

