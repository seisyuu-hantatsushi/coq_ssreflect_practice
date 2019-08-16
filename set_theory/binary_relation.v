From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import class_set.

Definition BinaryRelation (U:Type) := U -> U -> Prop.

Section BinaryRelation.

  Variable U:Type.
  Variable R: BinaryRelation U.

  Definition reflexive : Prop := forall (x:U), R x x.
  Definition transitive : Prop := forall (x y z:U), R x y -> R y z -> R x z.
  Definition symmetric : Prop := forall (x y:U), R x y -> R y x.
  Definition antisymmetric : Prop := forall (x y:U), R x y -> R y x -> x = y.

  Definition equivalence := reflexive /\ transitive /\ symmetric.

End BinaryRelation.
