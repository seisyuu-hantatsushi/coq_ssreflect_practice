From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import class_set.

Section BinaryRelation.

  Variable U:Type.

  Definition BinaryRelation := U -> U -> Prop.

  Inductive Graph (A B: Ensemble U) (R:BinaryRelation): Ensemble (Ensemble (Ensemble U)) :=
  | Definition_of_Graph: forall (x y:U), R x y /\ (|x, y|) ∈ A × B -> (|x, y|) ∈ Graph A B R.

  Definition reflexive : Prop := forall (x:U) (R:BinaryRelation), R x x.
  Definition transitive : Prop := forall (x y z:U) (R:BinaryRelation), R x y -> R y z -> R x z.
  Definition symmetric : Prop := forall (x y:U) (R:BinaryRelation), R x y -> R y x.
  Definition antisymmetric : Prop := forall (x y:U) (R:BinaryRelation), R x y -> R y x -> x = y.

  Definition equiv := reflexive /\ transitive /\ symmetric.

End BinaryRelation.
