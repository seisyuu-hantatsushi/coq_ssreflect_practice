From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import logic_theories.
Require Import logic_pred_theories.
Require Import class_set.
Require Import class_set_theories.

Section Direct_Product_Theories.

  Variable U:Type.

  Theorem ordered_pair_in_direct_product_iff_and:
    forall (A B:Ensemble U) (a b:U), (|a,b|) ∈ A × B <-> a ∈ A /\ b ∈ B.
  Proof.
    move => A B a b.
    rewrite /iff.
    split.
    move => H.
    inversion H.
    inversion H0.
    inversion H2 as [y].
    inversion H3.
    inversion H5.
    fold (OrderedPair x y) in H7.
    move: H7.
    rewrite (ordered_pair_iff a b x y).
    case => H7 H8.
    rewrite H7.
    rewrite H8.
    split.
    apply H4.
    apply H6.
    case => [H0 H1].
    split.
    exists a.
    exists b.
    split.
    apply H0.
    split.
    apply H1.
    fold (OrderedPair a b).
    reflexivity.
  Qed.

  Theorem direct_product_empty_r: forall (X:Ensemble U), X × {||} = {||}.
  Proof.
    move => X.
    apply /Extensionality_Ensembles.
    split => Y.
    -case.
     move => Z.
     case => [x [y [H1 [H2 H3]]]].
     rewrite H3.
     apply NNPP.
     rewrite /not => H4.
     move: H2.
     apply Noone_in_empty.
    -move => H0.
     apply NNPP.
     rewrite /not => H1.
     move: H0.
     apply Noone_in_empty.
  Qed.

  Theorem direct_product_empty_l: forall (X:Ensemble U), {||} × X = {||}.
  Proof.
    move => X.
    apply /Extensionality_Ensembles.
    split => Y.
    move => H0.
    apply NNPP.
    rewrite /not => H1.
    move: H0.
    case => Z.
    case => [x [y]].
    case => [H2 [H3 H4]].
    move : H2.
    apply Noone_in_empty.
    move => H0.
    apply NNPP.
    rewrite /not => H1.
    move: H0.
    apply Noone_in_empty.
  Qed.

  Theorem direct_product_empty_comm: forall (X:Ensemble U), {||} × X =  X × {||}.
  Proof.
    move => X.
    rewrite direct_product_empty_r.
    rewrite direct_product_empty_l.
    reflexivity.
  Qed.

  Theorem direct_product_empty_iff:
    forall (X Y:Ensemble U), X × Y = {||} <-> X = {||} \/ Y = {||}.
  Proof.
    move => X Y.
    rewrite /iff.
    split.
    +apply contrapositive.
     apply classic.
     move => H.
     ++suff: ~(forall (x y:U), ~((|x,y|) ∈ X × Y)).
       move => H0 H1.
       apply H0.
       rewrite H1.
       move => x y.
       apply Noone_in_empty.
     ++suff: exists x y:U, (|x,y|) ∈ X × Y.
       case => [x [y]].
       move => H0.
       unfold not.
       move => H1.
       move: H0.
       apply H1.
     ++suff: exists x y:U, x ∈ X /\ y ∈ Y.
       case => [x [y [HX HY]]].
       exists x.
       exists y.
       rewrite ordered_pair_in_direct_product_iff_and.
       split.
       apply HX.
       apply HY.
     ++suff: (exists x:U, x ∈ X) /\ (exists y:U, y ∈ Y).
       case.
       case => [x HX [y HY]].
       exists x.
       exists y.
       split.
       apply HX.
       apply HY.
     ++split; apply not_all_not_ex; unfold not; rewrite -Axiom_of_EmptySet; move => H1; apply H.
       left.
       apply H1.
       right.
       apply H1.
    +case => H; rewrite H.
     rewrite direct_product_empty_l.
     reflexivity.
     rewrite direct_product_empty_r.
     reflexivity.
  Qed.

  Theorem direct_product_included_iff:
    forall (X Y W Z:Ensemble U), W × Z ⊂ X × Y <-> W × Z = {||} \/ (W ⊂ X /\ Z ⊂ Y).
  Proof.
    +move => X Y W Z.
     rewrite /iff.
     split.
     move => H.
     (* W × Z ⊂ X × Y -> forall (t s:U), (|t,s|) ∈ W × Z -> (|t,s|) ∈ X × Y *)
     ++have L0: forall (t s:U), (|t,s|) ∈ W × Z -> (|t,s|) ∈ X × Y.
       move => t s.
       unfold Included in H.
       apply H.
     (* (forall (t s:U), (|t,s|) ∈ W × Z -> (|t,s|) ∈ X × Y) -> (forall (t s:U), ((t ∈ W /\ s ∈ Z) -> (t ∈ X /\ s ∈ Y))) *)
     ++have L1: forall (t s:U), ((t ∈ W /\ s ∈ Z) -> (t ∈ X /\ s ∈ Y)).
       move => t s.
       rewrite -!ordered_pair_in_direct_product_iff_and.
       apply L0.
     (* (forall (t s:U), ((t ∈ W /\ s ∈ Z) -> (t ∈ X /\ s ∈ Y))) -> (forall (t s:U), ((t ∈ W /\ s ∈ Z) -> t ∈ X) /\ ((t ∈ W /\ s ∈ Z) -> s ∈ Y)) *)
     ++have L2: forall (t s:U), ((t ∈ W /\ s ∈ Z) -> t ∈ X) /\ ((t ∈ W /\ s ∈ Z) -> s ∈ Y).
       move => t s.
       split; apply L1.
     (*  forall (t s:U), ((t ∈ W /\ s ∈ Z) -> t ∈ X) /\ ((t ∈ W /\ s ∈ Z) -> s ∈ Y) -> forall (t s:U), ((t ∈ W -> False) \/ (s ∈ Z -> False) \/ t ∈ X) /\ ((t ∈ W -> False) \/ (s ∈ Z -> False) \/ s ∈ Y) *)
     ++have L3: forall (t s:U), ((t ∈ W -> False) \/ (s ∈ Z -> False) \/ t ∈ X) /\ ((t ∈ W -> False) \/ (s ∈ Z -> False) \/ s ∈ Y).
       move => t0 s0.
       +++have L31: ((t0 ∈ W /\ s0 ∈ Z) -> False) <-> (t0 ∈ W -> False) \/ (s0 ∈ Z -> False).
          rewrite /iff.
          split; move => HF.
          apply not_and_or.
          unfold not.
          apply HF.
          apply or_not_and.
          unfold not.
          apply HF.
       +++have L32: forall (P:Prop), (((t0 ∈ W -> False) \/ (s0 ∈ Z -> False)) \/ P) <-> ((t0 ∈ W -> False) \/ (s0 ∈ Z -> False) \/ P).
          move => P.
          rewrite /iff.
          split.
          case.
          move => HL1.
          inversion HL1.
          left.
          apply H0.
          right.
          left.
          apply H0.
          move => HL1.
          right.
          right.
          apply HL1.
          move => HL1.
          inversion HL1.
          left.
          left.
          apply H0.
          inversion H0.
          left.
          right.
          apply H1.
          right.
          apply H1.
     ++rewrite -!L32.
       rewrite -L31.
       rewrite !or_not_l_iff_2.
       apply L2.
       apply classic.
       apply classic.
     (* forall (t s:U), ((t ∈ W -> False) \/ (s ∈ Z -> False) \/ t ∈ X) /\ ((t ∈ W -> False) \/ (s ∈ Z -> False) \/ s ∈ Y) ->
        forall (t s:U), ((t ∈ W -> t ∈ X) \/ (s ∈ Z -> False)) /\ ((s ∈ Z -> s ∈ Y) \/ (t ∈ W -> False)) *)
     ++have L4: forall (t s:U), ((t ∈ W -> t ∈ X) \/ (s ∈ Z -> False)) /\ ((s ∈ Z -> s ∈ Y) \/ (t ∈ W -> False)).
       move => t s.
       rewrite -(or_not_l_iff_1 (t ∈ W) (t ∈ X)).
       rewrite or_assoc.
       rewrite (or_comm (t ∈ X) (s ∈ Z -> False)).
       rewrite -(or_not_l_iff_1 (s ∈ Z) (s ∈ Y)).
       rewrite or_assoc.
       rewrite (or_comm (s ∈ Y) (t ∈ W -> False)).
       rewrite -(or_assoc (s ∈ Z -> False) (t ∈ W -> False) (s ∈ Y)).
       rewrite (or_comm (s ∈ Z -> False) (t ∈ W -> False)).
       rewrite or_assoc.
       apply L3.
       apply classic.
       apply classic.
    (* (forall (t s:U), ((t ∈ W -> t ∈ X) \/ (s ∈ Z -> False)) /\ ((s ∈ Z -> s ∈ Y) \/ (t ∈ W -> False))) ->
       forall (t s:U), ((t ∈ W -> t ∈ X) \/ (s ∈ Z -> False))) /\ (forall (t s:U),((s ∈ Z -> s ∈ Y) \/ (t ∈ W -> False)) *)
    +have L5: (forall (t s:U), ((t ∈ W -> t ∈ X) \/ (s ∈ Z -> False))) /\ (forall (t s:U),((s ∈ Z -> s ∈ Y) \/ (t ∈ W -> False))).
     split; apply L4.
    (*
       (forall (t s:U), ((t ∈ W -> t ∈ X) \/ (s ∈ Z -> False))) /\ (forall (t s:U),((s ∈ Z -> s ∈ Y) \/ (t ∈ W -> False))))
       ->
       ((forall (t:U), (t ∈ W -> t ∈ X)) \/ forall (s:U), (s ∈ Z -> False)) /\ ((forall (s:U), (s ∈ Z -> s ∈ Y)) \/ (forall (t:U), (t ∈ W -> False)))
     *)
    +have L6: ((forall (t:U), (t ∈ W -> t ∈ X)) \/ (forall (s:U), (s ∈ Z -> False))) /\
              ((forall (s:U), (s ∈ Z -> s ∈ Y)) \/ (forall (t:U), (t ∈ W -> False))).
     move: L5.
     case.
     move => L61 L62.
     split; apply forall_bound_or_dist_2.
     apply L61.
     move => t s.
     apply L62.
    +fold (Included U W X) in L6.
     fold (Included U Z Y) in L6.
     move : L6.
     rewrite -(Axiom_of_EmptySet Z).
     rewrite -(Axiom_of_EmptySet W).
     move => L6.
     rewrite direct_product_empty_iff.
     apply or_dist_and.
     ++suff: (Z={||} \/ W ⊂ X) /\ (W={||} \/ Z ⊂ Y).
       case.
       move => H0 H1.
       split.
       inversion H0.
       left.
       right.
       apply H2.
       right.
       apply H2.
       inversion H1.
       left.
       left.
       apply H2.
       right.
       apply H2.
     rewrite (or_comm (Z={||}) (W ⊂ X)).
     rewrite (or_comm (W={||}) (Z ⊂ Y)).
     apply L6.
    +case.
     move => H.
     rewrite H.
     apply Included_Empty.
     case => H0 H1.
     unfold Included.
     move => S.
     case => [T [x [y [HxW [HyZ HT]]]]].
     rewrite HT.
     apply ordered_pair_in_direct_product_iff_and.
     split.
     move: HxW.
     apply H0.
     move: HyZ.
     apply H1.
  Qed.

  Theorem direct_product_eq_to_or:
    forall (A B C D:Ensemble U), A × B = C × D -> A × B = {||} \/ C × D = {||} \/ (A = C /\ B = D).
  Proof.
    +move => A B C D H.
     ++have L0: (A × B ⊂ C × D) /\ (C × D ⊂ A × B).
       apply Extension.
       apply H.
    +inversion L0 as [LH0 LH1].
     apply imp_not_l.
     apply classic.
     move => H0.
     apply imp_not_l.
     apply classic.
     move => H1.
     ++suff: (A ⊂ C /\ B ⊂ D) /\ (C ⊂ A /\ D ⊂ B).
       case => [[H2 H3] [H4 H5]].
       split.
       apply /Extensionality_Ensembles.
       unfold Same_set.
       split.
       apply H2.
       apply H4.
       apply /Extensionality_Ensembles.
       unfold Same_set.
       split.
       apply H3.
       apply H5.
    +split.
     move: H0.
     apply imp_not_l.
     apply classic.
     apply direct_product_included_iff.
     apply LH0.
     move: H1.
     apply imp_not_l.
     apply classic.
     apply direct_product_included_iff.
     apply LH1.
  Qed.

  Theorem direct_product_or_eq:
    forall (A B C D:Ensemble U), (A × B = {||} /\ C × D = {||}) \/ (A = C /\ B = D) -> A × B = C × D.
  Proof.
    move => A B C D.
    case => H; inversion H; rewrite H0; rewrite H1; reflexivity.
  Qed.

  Theorem direct_product_included_right:
    forall (X Y Z:Ensemble U), ~(X={||}) /\ X × Z ⊂ X × Y -> Z ⊂ Y.
  Proof.
    move => X Y Z.
    case => HFX.
    rewrite direct_product_included_iff.
    rewrite direct_product_empty_iff.
    case.
    case.
    apply contrapositive.
    apply classic.
    move => H.
    apply HFX.
    move => H.
    rewrite H.
    apply Included_Empty.
    case => H.
    apply.
  Qed.

  Theorem direct_product_included_partial:
    forall (X Y Z:Ensemble U), Z ⊂ Y -> X × Z ⊂ X × Y.
  Proof.
    move => X Y Z H.
    apply direct_product_included_iff.
    right.
    split => x.
    apply.
    apply H.
  Qed.

  Theorem direct_product_union_dist_r:
    forall (X Y Z:Ensemble U), X × (Y ∪ Z) = X × Y ∪ X × Z.
  Proof.
    move => X Y Z.
    apply /Extensionality_Ensembles.
    +split => S.
     case => T.
     case => [x [y [H1 [H2 H3]]]].
     inversion H2.
     ++left.
       rewrite H3.
       apply ordered_pair_in_direct_product_iff_and.
       split.
       apply H1.
       apply H.
     ++right.
       rewrite H3.
       apply ordered_pair_in_direct_product_iff_and.
       split.
       apply H1.
       apply H.
    +case; move => T; case => V; case => [x [y [H1 [H2 H3]]]]; rewrite H3; apply ordered_pair_in_direct_product_iff_and; split.
     apply H1.
     left.
     apply H2.
    +apply H1.
     right.
     apply H2.
  Qed.

  Theorem direct_product_intersection_dist_r:
    forall (X Y Z:Ensemble U), X × (Y ∩ Z) = X × Y ∩ X × Z.
  Proof.
    move => X Y Z.
    apply /Extensionality_Ensembles.
    split => S.
    +case => T.
     case => [x [y [H1 [H2 H3]]]].
     inversion H2 as [y0 H4 H5 H6].
     split; split; exists x; exists y.
     split.
     apply H1.
     split.
     apply H4.
     apply H3.
     split.
     apply H1.
     split.
     apply H5.
     apply H3.
    +case => T.
     case => V.
     case => [x [y [H1 [H2 H3]]]].
     rewrite H3.
     rewrite ordered_pair_in_direct_product_iff_and.
     case => [H4 H5].
     rewrite ordered_pair_in_direct_product_iff_and.
     split.
     apply H1.
     split.
     apply H2.
     apply H5.
  Qed.

  Goal forall (y:U) (X Y:Ensemble U), y ∈ Y -> Pr1 (X × Y) = X.
  Proof.
    move => y X Y HY.
    apply /Extensionality_Ensembles.
    split => x H.
    inversion H.
    inversion H0 as [y0].
    apply ordered_pair_in_direct_product_iff_and in H2.
    inversion H2.
    apply H3.
    split.
    exists y.
    apply ordered_pair_in_direct_product_iff_and.
    split.
    apply H.
    apply HY.
  Qed.

  Goal forall (x:U) (X Y:Ensemble U), x ∈ X -> Pr2 (X × Y) = Y.
  Proof.
    move => x X Y HX.
    apply /Extensionality_Ensembles.
    split => y H.
    inversion H.
    inversion H0 as [x0].
    apply ordered_pair_in_direct_product_iff_and in H2.
    inversion H2.
    apply H4.
    split.
    exists x.
    apply ordered_pair_in_direct_product_iff_and.
    split.
    apply HX.
    apply H.
  Qed.

End Direct_Product_Theories.

Export class_set_theories.
