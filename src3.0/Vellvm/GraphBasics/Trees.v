(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(* A tree is inductively defined upon a set of vertices and a set of arcs.      *)

Require Export Acyclic.
Require Export Connected.

Section TREE.

Variable A:Set.

Inductive Tree : @V_set A-> @A_set A-> Set :=
  | T_root : forall r : Vertex, Tree (V_single r) (@A_empty A)
  | T_leaf :
      forall (v : V_set) (a : A_set) (t : Tree v a) (f n : Vertex),
      v n -> ~ v f -> Tree (V_union (V_single f) v) (A_union (E_set n f) a)
  | T_eq :
      forall (v v' : V_set) (a a' : A_set),
      v = v' -> a = a' -> Tree v a -> Tree v' a'.

Lemma Tree_isa_graph : forall (v : V_set) (a : A_set), Tree v a -> Graph v a.
Proof.
        intros v a t; elim t; intros.
        apply G_eq with (v := V_union (V_single r) (@V_empty A)) (a := (@A_empty A)).
        autounfold.
        rewrite V_union_commut; apply V_union_neutral.

        trivial.

        apply G_vertex.
        apply G_empty.

        compute in |- *. tauto.

        apply G_edge.
        apply G_vertex; trivial.

        apply V_in_right; trivial.

        apply V_in_left; apply V_in_single.

        red in |- *; intros He; elim n0.
        rewrite <- He; trivial.

        red in |- *; intro; elim n0; apply (G_ina_inv2 v0 a0 H n f); trivial.

        red in |- *; intro; elim n0; apply (G_ina_inv1 v0 a0 H f n); trivial.

        apply G_eq with (v := v0) (a := a0); trivial.
Defined.

Lemma Tree_isa_connected :
 forall (v : V_set) (a : A_set), Tree v a -> Connected v a.
Proof.
        intros v a t; elim t; intros.
        apply C_isolated.

        apply C_leaf; auto.

        apply C_eq with (v := v0) (a := a0); trivial.
Qed.

Lemma Tree_isa_acyclic :
 forall (v : V_set) (a : A_set), Tree v a -> Acyclic v a.
Proof.
        intros v a t; elim t; intros.
        apply AC_eq with (v := V_union (V_single r) (@V_empty A)) (a := (@A_empty A)).
        autounfold.
        rewrite V_union_commut; apply V_union_neutral.

        trivial.

        apply AC_vertex.
        apply AC_empty.

        compute in |- *. tauto.

        apply AC_leaf; auto.

        apply AC_eq with (v := v0) (a := a0); trivial.
Qed.

End TREE.

Implicit Arguments Tree [A].

Section CONNECTED_AND_ACYCLIC.

Variable A:Set.
Variable eq_a_dec: forall x y : A, {x = y} + {x <> y}.

Lemma Acyclic_connected_isa_tree :
 forall (v : V_set) (a : @A_set A), Acyclic v a -> Connected v a -> Tree v a.
Proof.
        intros v a ac; elim ac; intros.
        elim (Connected_not_empty _ _ H); auto.

        apply T_eq with (v := V_single x) (a := @A_empty A).
        symmetry  in |- *; apply (C_minus_isolated_left eq_a_dec _ _ H0 x).
        apply V_in_left; apply V_in_single.

        intros; red in |- *; intros; elim n.
        apply (AC_ina_inv1 _ _ _ _ ac0 H1).

        symmetry  in |- *; apply (C_minus_isolated_right eq_a_dec _ _ H0 x).
        apply V_in_left; apply V_in_single.

        intros; red in |- *; intros; elim n.
        apply (AC_ina_inv1 _ _ _ _ ac0 H1).

        apply T_root.

        apply T_leaf.
        apply H.
        apply (C_minus_pendant eq_a_dec _ _ H0 x y).
        apply V_in_right; trivial.

        apply V_in_left; apply V_in_single.

        intros.
        inversion H1.
        inversion H2; trivial.

        elim n; apply (AC_ina_inv1 _ _ y z ac0 H2).

        trivial.

        trivial.

        red in |- *; intros H1; elim n; apply (AC_ina_inv2 _ _ x y ac0 H1).

        red in |- *; intros H1; elim n; apply (AC_ina_inv1 _ _ y x ac0 H1).

        trivial.

        trivial.

        trivial.

        apply T_eq with (v := v0) (a := a0).
        trivial.

        trivial.

        apply H; apply C_eq with (v := v') (a := a'); auto.
Qed.

End CONNECTED_AND_ACYCLIC.

