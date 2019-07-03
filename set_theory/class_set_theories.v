From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import class_set.

Section Class_Set_Theories.

  Variable U:Type.

  Theorem union_comm:
    forall (X Y:Ensemble U), X ∪ Y = Y ∪ X.
  Proof.
    move => X Y.
    apply /Extensionality_Ensembles.
    +split => x; case => x0 H.
     ++right.
       apply H.
       left.
       apply H.
     ++right.
       apply H.
       left.
       apply H.
  Qed.

End Class_Set_Theories.

Export class_set.
