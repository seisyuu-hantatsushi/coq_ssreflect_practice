From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import class_set.

Section Class_Set_Theories.

  Variable U:Type.

  Theorem direct_product_and_iff:
    forall (x y:U) (X Y:Ensemble U), (|x,y|) ∈ (X × Y) <-> x ∈ X /\ y ∈ Y.
  Proof.
    rewrite /iff.
    split.
    (* (|x,y|) ∈ (X × Y) -> x ∈ X /\ y ∈ Y *)
    +move => H.
     inversion H.
     inversion H0.
     inversion H2 as [y0].
     inversion H3.
     inversion H5.
     move: H7.
     rewrite ordered_pair_iff.
     case => H7 H8.
     rewrite H7.
     rewrite H8.
     split.
     apply H4.
     apply H6.
    (* x ∈ X /\ y ∈ Y -> (|x,y|) ∈ (X × Y) *)
    +case => HX HY.
     split.
     exists x.
     exists y.
     split.
     apply HX.
     split.
     apply HY.
     unfold OrderedPair.
     reflexivity.
  Qed.

  Goal forall (y:U) (X Y:Ensemble U), y ∈ Y -> Pr1 (X × Y) = X.
  Proof.
    move => y X Y HY.
    apply /Extensionality_Ensembles.
    split => x H.
    inversion H.
    inversion H0 as [y0].
    apply direct_product_and_iff in H2.
    inversion H2.
    apply H3.
    split.
    exists y.
    apply direct_product_and_iff.
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
    apply direct_product_and_iff in H2.
    inversion H2.
    apply H4.
    split.
    exists x.
    apply direct_product_and_iff.
    split.
    apply HX.
    apply H.
  Qed.

End Class_Set_Theories.

Export class_set.