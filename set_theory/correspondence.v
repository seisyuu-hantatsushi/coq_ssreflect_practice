From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import logic_pred_theories.
Require Import class_set.
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
    case => X0.
    case.
    move => x H.
    inversion H.
    inversion H0.
    inversion H2.
    rewrite H1 in H4.
    