Require Import Metatheory.
Require Import Kildall.

Module Dom_Kildall.

Module DomDS := Dataflow_Solver_Var_Top(AtomNodeSet).

Section A.

Variable bound : ListSet.set atom.

Definition answer := Maps.AMap.t (DomDS.dt bound).

End A.

End Dom_Kildall.

