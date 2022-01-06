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
  Definition total_relation: Prop := forall (x y:U), R x y \/ R y x.

  Definition equivalence := reflexive /\ transitive /\ symmetric.
  Definition pre_order := reflexive /\ transitive.
  Definition partiality_order :=  pre_order /\ antisymmetric.
  Definition total_order := partiality_order /\ total_relation.

  Definition right_unique: Prop := forall (x y z:U), R x y -> R x z -> y = z.
  Definition left_total: Prop := forall (x:U), exists y:U, R x y.
  Definition functional_relaton: Prop := right_unique /\ left_total.

End BinaryRelation.
