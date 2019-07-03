From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import logic_pred_theories.
Require Import class_set.
Require Import direct_product_theories.
Require Import binary_relation.

Section Correspondence.
  Variable U: Type.

  Goal forall (A B:Ensemble U) (R:BinaryRelation U), GraphOfBinaryRelation A B R ⊂ A × B.
  Proof.
    move => A B R X.
    case => [x y [H]].
    apply.
  Qed.

  Inductive Domain (f:Ensemble (Ensemble (Ensemble U))) : Ensemble U :=
  | Definition_of_Domain: forall (x:U), x ∈ Pr1 f -> x ∈ Domain f.

  Inductive Range (f:Ensemble (Ensemble (Ensemble U))) : Ensemble U :=
  | Definition_of_Range: forall (y:U), y ∈ Pr2 f -> y ∈ Range f.

  Goal forall (A B:Ensemble U) (R:BinaryRelation U), Domain (GraphOfBinaryRelation A B R) ⊂ A.
  Proof.
    move => A B R X.
    case => [Z [x [y H]]].
    inversion H.
    inversion H1.
    rewrite H0 in H3.
    apply ordered_pair_in_direct_product_iff_and in H3.
    inversion H3.
    apply H4.
  Qed.

  Goal forall (A B:Ensemble U) (R:BinaryRelation U), Range (GraphOfBinaryRelation A B R) ⊂ B.
  Proof.
    move => A B R X.
    case => [Z [y [x H]]].
    inversion H.
    inversion H1.
    rewrite H0 in H3.
    apply ordered_pair_in_direct_product_iff_and in H3.
    inversion H3.
    apply H5.
  Qed.

  Inductive Image (f:Ensemble (Ensemble (Ensemble U))) (C:Ensemble U) : Ensemble U :=
  | Definition_of_Image: forall  (y:U), (exists x:U, x ∈ C /\ (|x,y|) ∈ f) -> y ∈ Image f C.

  Goal forall (A B C:Ensemble U) (R:BinaryRelation U),
      forall y:U, (y ∈ Image (GraphOfBinaryRelation A B R) C) <-> exists x:U, (x ∈ C /\ (|x, y|) ∈ GraphOfBinaryRelation A B R).
  Proof.
    move => A B C R y.
    rewrite /iff.
    split.
    case => y0.
    apply.
    case => [x [HxC H]].
    split.
    exists x.
    split.
    apply HxC.
    apply H.
  Qed.

End Correspondence.
