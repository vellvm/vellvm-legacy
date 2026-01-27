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



(* Different definitions of pathes in a directed graph.                 *)

(* The following notions are defined :                                  *)
(*      - D_walk : list of vertices joined one by one by arcs,          *)
(*                constructors : DW_null, DW_step;                      *)
(*      - D_trail : walk without repetition of arcs,                    *)
(*              constructors : DT_null, DT_step;                        *)
(*      - D_path : trail without repetition of inner vertices,          *)
(*              constructors : DP_null, DP_step;                        *)
(*      - D_closed_walk, D_closed_trail, D_cycle.                       *)

Require Export Digraphs.

Section DIRECTED_PATHES.

Variable A:Set.
Variable v : @V_set A.
Variable a : @A_set A.

Inductive D_walk : @Vertex A-> @Vertex A-> @V_list A-> @A_list A-> Prop :=
  | DW_null : forall x : Vertex, v x -> D_walk x x V_nil A_nil
  | DW_step :
      forall (x y z : Vertex) (vl : V_list) (al : A_list),
      D_walk y z vl al ->
      v x -> a (A_ends x y) -> D_walk x z (y :: vl) (A_ends x y :: al).

Definition D_closed_walk :=
  forall (x : Vertex) (vl : V_list) (al : A_list), D_walk x x vl al.

Inductive D_trail : @Vertex A-> @Vertex A-> @V_list A-> @A_list A-> Prop :=
  | DT_null : forall x : Vertex, v x -> D_trail x x V_nil A_nil
  | DT_step :
      forall (x y z : Vertex) (vl : V_list) (al : A_list),
      D_trail y z vl al ->
      v x ->
      a (A_ends x y) ->
      ~ In (A_ends x y) al -> D_trail x z (y :: vl) (A_ends x y :: al).

Definition D_closed_trail :=
  forall (x : Vertex) (vl : V_list) (al : A_list), D_trail x x vl al.

Inductive D_path : @Vertex A-> @Vertex A-> @V_list A-> @A_list A-> Prop :=
  | DP_null : forall x : Vertex, v x -> D_path x x V_nil A_nil
  | DP_step :
      forall (x y z : Vertex) (vl : V_list) (al : A_list),
      D_path y z vl al ->
      v x ->
      a (A_ends x y) ->
      x <> y ->
      ~ In y vl ->
      (In x vl -> x = z) ->
      ~ In (A_ends x y) al -> D_path x z (y :: vl) (A_ends x y :: al).

Definition D_cycle :=
  forall (x : Vertex) (vl : V_list) (al : A_list), D_path x x vl al.


Lemma D_trail_isa_walk :
 forall (x y : Vertex) (vl : V_list) (al : A_list) (t : D_trail x y vl al),
 D_walk x y vl al.
Proof.
        intros x y vl al t; elim t; intros.
        apply DW_null; trivial.

        apply DW_step; trivial.
Qed.

Lemma D_path_isa_trail :
 forall (x y : Vertex) (vl : V_list) (al : A_list) (p : D_path x y vl al),
 D_trail x y vl al.
Proof.
        intros x y vl al p; elim p; intros.
        apply DT_null; trivial.

        apply DT_step; trivial.
Qed.

Lemma D_path_isa_walk :
 forall (x y : Vertex) (vl : V_list) (al : A_list) (p : D_path x y vl al),
 D_walk x y vl al.
Proof.
   intros. apply D_trail_isa_walk. apply D_path_isa_trail; auto.
Qed.

Lemma DW_iny_vl :
 forall (x y : Vertex) (vl : V_list) (al : A_list),
 D_walk x y vl al -> vl <> V_nil -> In y vl.
Proof.
        intros x y vl al d; elim d; intros.
        absurd (V_nil = @V_nil A); auto.

        inversion H.
        simpl in |- *; auto.

        rewrite H9; simpl in |- *; right.
        apply H0; rewrite <- H9; discriminate.
Qed.

Lemma DW_endx_inv :
 forall (x y : Vertex) (vl : V_list) (al : A_list), D_walk x y vl al -> v x.
Proof.
        intros x y vl el d; elim d; auto.
Qed.

Lemma DW_endy_inv :
 forall (x y : Vertex) (vl : V_list) (al : A_list), D_walk x y vl al -> v y.
Proof.
        intros x y vl el d; elim d; auto.
Qed.

Lemma DW_invl_inv :
 forall (x y : Vertex) (vl : V_list) (al : A_list),
 D_walk x y vl al -> forall z : Vertex, In z vl -> v z.
Proof.
        intros x y vl al d; elim d; intros.
        inversion H0.

        inversion H3; subst; auto.
        apply (DW_endx_inv _ _ _ _ H).
Qed.

Lemma DW_inel_ina :
 forall (x y : Vertex) (vl : V_list) (al : A_list),
 D_walk x y vl al ->
 forall x' y' : Vertex, In (A_ends x' y') al -> a (A_ends x' y').
Proof.
        intros x y vl el d; elim d; intros.
        inversion H0.

        inversion H3; auto.
        inversion H4; subst; auto.
Qed.

Lemma DW_inxyel_inxvl :
 forall (x y : Vertex) (vl : V_list) (al : A_list),
 D_walk x y vl al ->
 forall x' y' : Vertex, In (A_ends x' y') al -> In x' (x :: vl).
Proof.
        intros x y vl al d; elim d; intros.
        inversion H0.

        inversion H3.
          inversion H4.
          simpl in |- *; auto.

          simpl in |- *; right.
          apply (H0 x' y'); auto.
Qed.

Lemma DW_inxyel_inyvl :
 forall (x y : Vertex) (vl : V_list) (al : A_list),
 D_walk x y vl al ->
 forall x' y' : Vertex, In (A_ends x' y') al -> In y' (x :: vl).
Proof.
        intros x y vl el d; elim d; intros.
        inversion H0.

        inversion H3.
          inversion H4.
          simpl in |- *; auto.

          simpl in |- *; right.
          apply (H0 x' y'); auto.
Qed.

Lemma DW_backstep :
 forall (x y z : Vertex) (vl : V_list) (al : A_list),
 D_walk x z (y :: vl) al ->
   exists al' : A_list, D_walk y z vl al' /\ (al = (A_ends x y) ::al').
Proof.
        intros; inversion H.
        split with al0. split; auto.
Qed.

Lemma DW_neq_ends_inv :
 forall (x y : Vertex) (vl : V_list) (al : A_list),
 D_walk x y vl al -> x <> y -> vl <> V_nil /\ al <> A_nil.
Proof.
        intros; inversion H; subst; auto.
          split; intro J; inversion J.
Qed.

Lemma DW_Vnil_inv :
 forall (x y : Vertex) (al : A_list),
 D_walk x y V_nil al -> x = y /\ al = A_nil.
Proof.
        intros; inversion H; subst; auto.
Qed.

Lemma DW_Anil_inv :
 forall (x y : Vertex) (vl : V_list),
 D_walk x y vl A_nil -> x = y /\ vl = V_nil.
Proof.
        intros; inversion H; subst; auto.
Qed.

Lemma DP_iny_vl :
 forall (x y : Vertex) (vl : V_list) (al : A_list),
 D_path x y vl al -> vl <> V_nil -> In y vl.
Proof.
        intros x y vl al d; elim d; intros.
        absurd (V_nil = @V_nil A); auto.

        inversion H.
          simpl in |- *; auto.

          rewrite H17; simpl in |- *; right.
          apply H0; rewrite <- H17; discriminate.
Qed.

Lemma DP_endx_inv :
 forall (x y : Vertex) (vl : V_list) (al : A_list), D_path x y vl al -> v x.
Proof.
        intros x y vl el d; elim d; auto.
Qed.

Lemma DP_endy_inv :
 forall (x y : Vertex) (vl : V_list) (al : A_list), D_path x y vl al -> v y.
Proof.
        intros x y vl el d; elim d; auto.
Qed.

Lemma DP_invl_inv :
 forall (x y : Vertex) (vl : V_list) (al : A_list),
 D_path x y vl al -> forall z : Vertex, In z vl -> v z.
Proof.
        intros x y vl al d; elim d; intros.
        inversion H0.

        inversion H7; subst; auto.
        apply (DP_endx_inv _ _ _ _ H).
Qed.

Lemma DP_inel_ina :
 forall (x y : Vertex) (vl : V_list) (al : A_list),
 D_path x y vl al ->
 forall x' y' : Vertex, In (A_ends x' y') al -> a (A_ends x' y').
Proof.
        intros x y vl el d; elim d; intros.
        inversion H0.

        inversion H7; subst; auto.
        inversion H8; subst; auto.
Qed.

Lemma DP_inxyel_inxvl :
 forall (x y : Vertex) (vl : V_list) (al : A_list),
 D_path x y vl al ->
 forall x' y' : Vertex, In (A_ends x' y') al -> In x' (x :: vl).
Proof.
        intros x y vl al d; elim d; intros.
        inversion H0.

        inversion H7.
          inversion H8; subst.
          simpl in |- *; auto.

          simpl in |- *; right.
          apply (H0 x' y'); auto.
Qed.

Lemma DP_inxyel_inyvl :
 forall (x y : Vertex) (vl : V_list) (al : A_list),
 D_path x y vl al ->
 forall x' y' : Vertex, In (A_ends x' y') al -> In y' (x :: vl).
Proof.
        intros x y vl el d; elim d; intros.
        inversion H0.

        inversion H7.
          inversion H8; subst.
          simpl in |- *; auto.

          simpl in |- *; right.
          apply (H0 x' y'); auto.
Qed.

Lemma DP_endx_ninV :
 forall (x y : Vertex) (vl : V_list) (al : A_list),
 D_path x y vl al -> x <> y -> ~ In x vl.
Proof.
  intros x y vl el d Hneq. inversion d; subst; simpl; auto.
  intro J.
  destruct J as [J | J]; subst; auto.
Qed.

Lemma DP_backstep :
 forall (x y z : Vertex) (vl : V_list) (al : A_list),
 D_path x z (y :: vl) al -> exists al' : A_list, D_path y z vl al'.
Proof.
        intros; inversion H.
        split with al0; trivial.
Qed.

Lemma DP_prefix_no_head:  forall (y z : Vertex) (vl : V_list) (al : A_list) 
 (H: D_path y z vl al), 
 vl = V_nil \/ (exists vl', vl = vl' ++ z::nil /\ ~ In z vl').
Proof.
  intros.
  induction H; auto.
    right.
    destruct IHD_path as [J | [vl' [J1 J2]]]; subst.
      inversion H; subst.
      exists nil. split; auto.

      exists (y::vl').
      split; auto.
        simpl.
        intro J.
        destruct J as [J | J]; subst; auto.
          apply H3. apply in_or_app; simpl; auto.
Qed.

End DIRECTED_PATHES.

Implicit Arguments D_walk [A].
Implicit Arguments DW_backstep [A].
Implicit Arguments D_path [A].
Implicit Arguments DP_backstep [A].
Implicit Arguments DP_endx_inv [A].
Implicit Arguments DP_inxyel_inxvl [A].

Require Export Paths.

Section DEXTRACTED.

Variable A:Set.
Variable eq_a_dec: forall x y : A, {x = y} + {x <> y}.

Variable v : @V_set A.
Variable a : @A_set A.

Lemma DW_extract :
 forall (x y z : Vertex) (vl : V_list) (al : A_list),
 D_walk v a y z vl al ->
 In x (y :: vl) ->
 exists al' : A_list, D_walk v a x z (V_extract eq_a_dec x (y :: vl)) al'.
Proof.
        intros x y z vl; generalize y; elim vl; simpl in |- *; intros.
        split with al.
        replace x with y0; auto.
        case (V_in_dec eq_a_dec y0 nil); auto.

        tauto.

        elim (DW_backstep _ _ _ _ _ _ _ H0); intros.
        destruct H2 as [H2 Heq]; subst.
        case (V_in_dec eq_a_dec x (a0 :: l)). intros.
        apply (H a0 x0); auto.

        simpl in |- *. intros.
        split with (A_ends y0 a0 :: x0).
        replace x with y0.
          trivial.

          tauto.
Qed.

Lemma DW_cut :
 forall (y z: Vertex) (vl : V_list) (al : A_list),
 D_walk v a y z vl al -> vl <> V_nil ->
 forall x w,
 In x (y :: vl) ->
 In w (y :: vl) ->
 x <> y -> w <> y -> x <> w ->
    exists al1 : A_list, exists al2 : A_list, exists vl1 : V_list,
    exists vl2 : V_list,
      (D_walk v a y x vl1 al1 /\ D_walk v a x z vl2 al2 /\
       (al1 ++ al2 = al) /\ (vl1 ++ vl2 = vl) /\ ~ In w (y::vl1)) \/
      (D_walk v a y w vl1 al1 /\ D_walk v a w z vl2 al2 /\
       (al1 ++ al2 = al) /\ (vl1 ++ vl2 = vl) /\ ~ In x (y::vl1)).
Proof.
  induction 1; simpl in *; intros.
    congruence.

    destruct H3 as [H3 | H3]; try congruence; subst.
    destruct H4 as [H4 | H4]; try congruence; subst.
    destruct vl.
      inversion H; subst.
      destruct H3 as [H3 | H3]; try solve [inversion H3]; subst.
      destruct H4 as [H4 | H4]; try solve [inversion H4]; subst.
      congruence.

      destruct (V_eq_dec eq_a_dec y w); subst.
        exists (A_ends x w::nil). exists al. exists (w::nil). exists (v0::vl).
        right.
        split. constructor; auto. constructor; auto. apply DW_endx_inv in H; auto.
        split; auto.
        split; auto.
        split; auto.
          intro J.
          destruct J as [J | J]; subst.
            congruence.
            simpl in J.
            destruct J as [J | J]; subst; auto.

      destruct (V_eq_dec eq_a_dec y x0); subst.
        exists (A_ends x x0::nil). exists al. exists (x0::nil). exists (v0::vl).
        left.
        split. constructor; auto. constructor; auto. apply DW_endx_inv in H; auto.
        split; auto.
        split; auto.
        split; auto.
          intro J.
          destruct J as [J | J]; subst.
            congruence.
            simpl in J.
            destruct J as [J | J]; subst; auto.

          eapply IHD_walk in H3; eauto.
            clear IHD_walk.
            destruct H3 as [al1 [al2 [vl1 [vl2
              [[J1 [J2 [J3 [J4 J5]]]]|[J1 [J2 [J3 [J4 J5]]]]]]]]]; subst.
              exists (A_ends x y::al1). exists al2. exists (y::vl1). exists vl2.
              right. rewrite <- J4.
              split. constructor; auto.
              split; auto.
              split; auto.
              split; auto.
                intro J.
                destruct J as [J | J]; subst.
                  congruence.
                  apply J5. simpl in J. auto.

              exists (A_ends x y::al1). exists al2. exists (y::vl1). exists vl2.
              left. rewrite <- J4.
              split. constructor; auto.
              split; auto.
              split; auto.
              split; auto.
                intro J.
                destruct J as [J | J]; subst.
                  congruence.
                  apply J5. simpl in J. auto.
            intro J. inversion J.
Qed.

Lemma DW_split :
 forall (x y z : Vertex) (vl : V_list) (al : A_list),
 D_walk v a y z vl al ->
 In x (y :: vl) ->
    exists al1 : A_list, exists al2 : A_list, exists vl1 : V_list,
    exists vl2 : V_list,
      D_walk v a y x vl1 al1 /\ D_walk v a x z vl2 al2 /\
      (al1 ++ al2 = al) /\ (vl1 ++ vl2 = vl).
Proof.
  intros.
  induction H.
    assert (x0 = x) as EQ.
      simpl in H0.
      destruct H0 as [H0 | H0]; inversion H0; auto.
    clear H0. subst.
    exists A_nil. exists A_nil. exists V_nil. exists V_nil.
    repeat split; try solve [auto | constructor; auto].

    destruct (V_eq_dec eq_a_dec x x0); subst.
      exists A_nil. exists (A_ends x0 y :: al). exists V_nil. exists (y::vl).
      repeat split; try solve [auto | constructor; auto].

      assert (In x (y::vl)) as Hin.
        simpl in H0.
        destruct H0 as [H0 | H0]; auto; try congruence.
      clear H0.
      apply IHD_walk in Hin.
      destruct Hin as [al1 [al2 [vl1 [vl2 [J1 [J2 [J3 J4]]]]]]]; subst.
      exists (A_ends x0 y::al1). exists al2. exists (y::vl1). exists vl2.
      repeat split; try solve [auto | constructor; auto].
Qed.

Lemma DP_extract :
 forall (x y z : Vertex) (vl : V_list) (al : A_list),
 D_path v a y z vl al ->
 In x (y :: vl) ->
 exists al' : A_list,  D_path v a x z (V_extract eq_a_dec x (y :: vl)) al'.
Proof.
        intros x y z vl; generalize y; elim vl; simpl in |- *; intros.
        split with al.
        replace x with y0; auto.
        case (V_in_dec eq_a_dec y0 nil); auto.

        tauto.

        elim (DP_backstep _ _ _ _ _ _ _ H0); intros.
        case (V_in_dec eq_a_dec x (a0 :: l)). intros.
        apply (H a0 x0); auto.

        simpl in |- *. intros. split with al. replace x with y0.
        trivial.

        tauto.
Qed.

Remark DP_when_cycle :
 forall (x y : Vertex) (vl : V_list) (al : A_list),
 D_path v a x y vl al -> In x vl -> x = y.
Proof.
        intros x y vl al H; inversion H; intros.
        trivial.

        inversion H11.
        absurd (x = y0); auto.

        auto.
Qed.

Lemma DP_split :
 forall v a (x y z : Vertex) (vl : V_list) (al : A_list) 
 (H: D_path v a y z vl al),
 In x (y :: vl) ->
    exists al1 : A_list, exists al2 : @A_list A, exists vl1 : V_list,
    exists vl2 : V_list,
      D_path v a y x vl1 al1 /\ D_path v a x z vl2 al2 /\
      (al1 ++ al2 = al) /\ (vl1 ++ vl2 = vl).
Proof.
  intros.
  induction H; intros.
    assert (x0 = x) as EQ.
      simpl in H0.
      destruct H0 as [H0 | H0]; inversion H0; auto.
    clear H0. subst.
    exists A_nil. exists A_nil. exists V_nil. exists V_nil.
    repeat split; try solve [auto | constructor; auto].

    destruct (V_eq_dec eq_a_dec x x0); subst.
      exists A_nil. exists (A_ends x0 y :: al). exists V_nil. exists (y::vl).
      repeat split; try solve [auto | constructor; auto].

      assert (In x (y::vl)) as Hin.
        simpl in H0.
        destruct H0 as [H0 | H0]; auto; try congruence.
      clear H0.
      apply IHD_path in Hin; auto.
      destruct Hin as [al1 [al2 [vl1 [vl2 [J1 [J2 [J3 J4]]]]]]]; subst.
      exists (A_ends x0 y::al1). exists al2. exists (y::vl1). exists vl2.
      repeat split; try solve [auto | constructor; auto].
      constructor; auto.
        intro J. apply H4. apply in_or_app. auto.

        intro J. 
        assert (In x0 (vl1++vl2)) as Hin. 
          apply in_or_app. auto.
        apply H5 in Hin. subst. 
        assert (J2':=J2).
        apply DP_prefix_no_head in J2'.
        destruct J2' as [EQ | [vl' [EQ Hnotin]]]; subst.
          inversion J2; subst; auto.
          
          apply DP_prefix_no_head in H.
          destruct H as [EQ | [v2' [EQ Hnotin']]]; subst.
            assert (In z V_nil) as G.
              rewrite <- EQ.
              apply in_or_app. right. apply in_or_app; simpl; auto.
            inversion G.
        
            rewrite app_assoc in EQ.
            apply app_inj_tail in EQ.
            destruct EQ; subst.
            contradict Hnotin'.
            apply in_or_app; auto.
        
        intro J. apply H6. apply in_or_app. auto.
Qed.

Lemma DWalk_to_dpath' :
 forall (x y : Vertex) (vl : V_list) (al : A_list),
 D_walk v a x y vl al ->
 exists vl0 : V_list, exists al0 : A_list, 
    D_path v a x y vl0 al0 /\
    (forall vx, In vx vl0 -> In vx vl).
Proof.
  intros x y vl al w; elim w; intros.
    split with V_nil; split with A_nil. 
    split; auto.
     apply DP_null; trivial.

    elim H0; clear H0; intros vl' H0.
    elim H0; clear H0; intros al' H0.
    destruct H0 as [H0 Hinv].           
    case (V_in_dec eq_a_dec x0 (y0 :: vl')); intros.
      elim (DP_extract _ _ _ _ _ H0 i); intros.
      split with (V_extract eq_a_dec x0 (y0 :: vl')); split with x1.
      split; auto.
        intros vx Hinvx.
        apply V_extract_spec'' in Hinvx.
        simpl in *.
        destruct Hinvx; auto.

      case (V_in_dec eq_a_dec y0 vl'); intros.
        split with (y0 :: V_nil); split with (A_ends x0 y0 :: A_nil).
        split; try solve [
           intros vx Hinvx; simpl in Hinvx; simpl; destruct Hinvx; 
           try solve [auto | tauto]
        ].
        apply DP_step.
          replace z with y0.
            apply DP_null; apply (DP_endx_inv _ _ _ _ _ _ H0).

            apply (DP_when_cycle _ _ _ _ H0); auto.

          trivial.

          trivial.

          red in |- *; intros; elim n; subst; simpl in |- *; auto.

          tauto.

          simpl in |- *. tauto.

          tauto.

        split with (y0 :: vl'); split with (A_ends x0 y0 :: al').
        split; try solve [
           intros vx Hinvx; simpl in Hinvx; simpl; destruct Hinvx; auto
        ].
        apply DP_step.
          trivial.

          trivial.

          trivial.

          red in |- *; intros; elim n; subst; simpl in |- *; auto.

          trivial.

          intros; absurd (In x0 vl').
            red in |- *; intros; elim n; simpl in |- *; auto.

            trivial.

            red in |- *; intros.
            elim n; inversion w; apply (DP_inxyel_inxvl _ _ _ _ _ _ H0 x0 y0); auto.
Qed.

Lemma DWalk_to_dpath :
 forall (x y : Vertex) (vl : V_list) (al : A_list),
 D_walk v a x y vl al ->
 exists vl0 : V_list, exists al0 : A_list, D_path v a x y vl0 al0.
Proof.
  intros.
  apply DWalk_to_dpath' in H.
  destruct H as [? [? [? ?]]]; eauto.
Qed.

End DEXTRACTED.

Implicit Arguments D_trail [A].

Section DPATH_EQ.

Variable A:Set.

Lemma DWalk_eq :
 forall (v v' : V_set) (a a' : @A_set A) (x y : Vertex)
   (vl : V_list) (al : A_list),
 D_walk v a x y vl al -> v = v' -> a = a' -> D_walk v' a' x y vl al.
Proof.
        intros; elim H; intros.
        apply DW_null.
        rewrite <- H0; trivial.

        apply DW_step.
        trivial.

        rewrite <- H0; trivial.

        rewrite <- H1; trivial.
Qed.

Lemma DTrail_eq :
 forall (v v' : V_set) (a a' : @A_set A) (x y : Vertex)
   (vl : V_list) (al : A_list),
 D_trail v a x y vl al -> v = v' -> a = a' -> D_trail v' a' x y vl al.
Proof.
        intros; elim H; intros.
        apply DT_null.
        rewrite <- H0; trivial.

        intros; apply DT_step.
        trivial.

        rewrite <- H0; trivial.

        rewrite <- H1; trivial.

        trivial.
Qed.

Lemma DPath_eq :
 forall (v v' : V_set) (a a' : @A_set A) (x y : Vertex)
   (vl : V_list) (al : A_list),
 D_path v a x y vl al -> v = v' -> a = a' -> D_path v' a' x y vl al.
Proof.
        intros; elim H; intros.
        apply DP_null.
        rewrite <- H0; trivial.

        intros; apply DP_step.
        trivial.

        rewrite <- H0; trivial.

        rewrite <- H1; trivial.

        trivial.

        trivial.

        trivial.

        trivial.
Qed.

End DPATH_EQ.

Section APPEND_DWALKS.

Variable A:Set.
Variable v : @V_set A.
Variable a : @A_set A.

Lemma DWalk_append :
 forall (x y z : Vertex) (vl vl' : V_list) (al al' : A_list),
 D_walk v a x y vl al ->
 D_walk v a y z vl' al' -> D_walk v a x z (vl ++ vl') (al ++ al').
Proof.
        intros x y z vl vl' al al' Hw; elim Hw; simpl in |- *; intros.
        trivial.

        apply DW_step; auto.
Qed.

End APPEND_DWALKS.

Lemma D_walk_iff: forall A v1 a1 x y vl al v2 a2
  (H1: forall x, v2 x <-> v1 x)
  (H2: forall x, a2 x <-> a1 x),
  @D_walk A v1 a1 x y vl al <->
  D_walk v2 a2 x y vl al.
Proof.
  intros.
  split; intro J.
    induction J; constructor; auto.
      apply H1; auto.
      apply H1; auto.
      apply H2; auto.
    induction J; constructor; auto.
      apply H1; auto.
      apply H1; auto.
      apply H2; auto.
Qed.

Lemma D_walk_sub: forall A x y vl al (v1 v2:@V_set A) (a1 a2:@A_set A)
  (H1: forall x, v2 x -> v1 x)
  (H2: forall x, a2 x -> a1 x)
  (J: @D_walk A v2 a2 x y vl al),
  D_walk v1 a1 x y vl al.
Proof.
  intros.
  induction J; constructor; auto.
Qed.

Require Import Metatheory.
Require Import util.
Require Import vellvm_tactics.

Lemma DW_last_split: forall (A:Set) 
  v a vl v1 v2 (al : @A_list A) 
  (Hw : D_walk v a v2 v1 (vl ++ v1::nil) al),
  exists v1', exists al',
    D_walk v a v2 v1' vl al' /\
    D_walk v a v1' v1 (v1::nil) (A_ends v1' v1::nil) /\
    al = al' ++ (A_ends v1' v1::nil).
Proof.
  induction vl; intros.
  (*base*)
    assert (v v1) as J.
      apply DW_endy_inv in Hw; auto.
    inversion Hw; subst. inversion H1; subst.
    exists v2. exists nil.
    split.
      constructor; auto.
    split; auto.
  (*ind*)
    inversion Hw; subst.
    apply IHvl in H1; auto.
    destruct H1 as [v1' [al2 [Hw1 [Hw2 EQ]]]]; subst.
    exists v1'. exists (A_ends v2 a0::al2).
    split; auto.
      constructor; auto. 
Qed.

Lemma DW_head_inversion :
 forall A v a (z: Vertex) (vl : @V_list A) (x: Vertex) (al : @A_list A)
 (Hw: D_walk v a x z vl al) (Hnnil: vl <> nil),
 exists y, exists vl', exists al',
   D_walk v a x y vl' al' /\
   vl = vl' ++ (z::nil) /\
   al = al' ++ (A_ends y z::nil) /\
   a (A_ends y z) /\ v y.
Proof.
  intros.
  apply nnil_inv in Hnnil.
  destruct Hnnil as [vl' [v' EQ]]; subst.
  generalize dependent x.
  generalize dependent al.
  induction vl'; intros.
  (*base*)
    assert (v z) as J.
      apply DW_endy_inv in Hw; auto.
    inversion Hw; subst. inversion H1; subst.
    exists x. exists nil. exists nil.
    split.
      constructor; auto.
    split; auto.
  (*ind*)
    inversion Hw; subst.
    apply IHvl' in H1; auto.
    destruct H1 as [v1' [vl2 [al2 [Hw1 [Hw2 [EQ1 [EQ2 J]]]]]]]; subst.
    exists v1'. exists (a0::vl2). exists (A_ends x a0::al2).
    split. constructor; auto. 
    split. simpl_env. rewrite Hw2. auto. 
    split; auto.
Qed.

Lemma DW_Forall_head: forall A v (a:@A_set A) v1 v2 vl al P 
  (Hw: D_walk v a v1 v2 vl al)
  (Hforall: Forall P (v1 :: vl)), P v2.
Proof.
  intros.
  apply Forall_forall with (x:=v2) in Hforall; auto.
  assert (Hw':=Hw).
  inversion Hw; subst.
    simpl; auto.

    apply DW_iny_vl in Hw'.
      simpl in *. tauto.

      intro J. inversion J.
Qed.

Lemma DW_split' :
 forall A v a (x z : Vertex) vl1 vl2 (vl : @V_list A) (al : @A_list A) 
 (y: Vertex),
 D_walk v a y z vl al ->
 vl = vl2 ++ x :: vl1 ->
    exists al1 : A_list, exists al2 : A_list, 
      D_walk v a x z vl1 al1 /\ D_walk v a y x (vl2 ++ [x]) al2 /\
      (al2 ++ al1 = al).
Proof.
  induction vl2; intros; subst.
  Case "base".
    inversion H; subst.
    exists al0. exists [A_ends y x].
    split; auto.
    split; auto.
      constructor; auto.
      constructor; auto.
        apply DW_endx_inv in H2; auto.
  Case "ind".
    simpl_env in H.
    inversion H; subst.
    apply IHvl2 in H2; auto.
    destruct H2 as [al1 [al2 [Hw1 [Hw2 EQ]]]]; subst.
    exists al1. exists (A_ends y a0::al2).
    split; auto.
    split; auto.
      simpl_env. simpl. constructor; auto.     
Qed.

Lemma DW_split'' :
 forall A v a (x z : Vertex) (vl : @V_list A) (al : @A_list A) 
 (y: Vertex) (Hw: D_walk v a y z vl al) (Hin: In x vl),
 exists vl2, exists vl1, exists al1 : A_list, exists al2 : A_list, 
   vl = vl2 ++ x :: vl1 /\
   D_walk v a x z vl1 al1 /\ D_walk v a y x (vl2 ++ [x]) al2 /\
   (al2 ++ al1 = al).
Proof.
  intros.
  apply in_split in Hin.
  destruct Hin as [vl2 [vl1 EQ]].
  exists vl2. exists vl1.
  eapply DW_split' in Hw; eauto.
  destruct Hw as [al1 [al2 [Hw1 [Hw2 EQ']]]].
  exists al1. exists al2. auto.
Qed.

Lemma DW_chunk :
 forall A v a (x z : Vertex) vl1 vl3 vl2 (vl : @V_list A) (al : @A_list A) 
 (y: Vertex) (Hw: D_walk v a y z vl al) 
 (EQ: y :: vl = vl2 ++ x :: vl3 ++ x :: vl1),
 exists al3 : A_list, D_walk v a x x (vl3 ++ [x]) al3.
Proof.
  intros.
  destruct vl2; inversion EQ; subst.
  Case "base".
    eapply DW_split' in Hw; eauto.
    destruct Hw as [al1 [al2 [Hw1 [Hw2 EQ']]]]; subst. eauto.
  Case "ind".
    eapply DW_split' in Hw; eauto.
    destruct Hw as [al1 [al2 [Hw1 [Hw2 EQ']]]]; subst. 
    eapply DW_split' in Hw1; eauto.
    destruct Hw1 as [al11 [al12 [Hw11 [Hw12 EQ']]]]; subst. eauto.
Qed.

Lemma D_walk_weakening: forall A x y vl al (v1 v2:@V_set A) (a1 a2:@A_set A)
  (H1: forall z, In z (x::vl) -> v1 z)
  (H2: forall z, In z al -> a1 z)
  (J: @D_walk A v2 a2 x y vl al),
  D_walk v1 a1 x y vl al.
Proof.
  intros.
  induction J; constructor.
    apply H1; simpl; auto.
    apply IHJ.
      intros. apply H1. simpl; auto.
      intros. apply H2. simpl; auto.
    apply H1; simpl; auto.
    apply H2; simpl; auto.
Qed.
 
