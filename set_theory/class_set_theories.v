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

  Lemma noone_in_complement: forall (x:U) (X:Ensemble U), x ∈ X <-> (x ∈ (X^c) -> False).
  Proof.
    move => x X.
    rewrite /iff.
    split => H.
    +move => H0.
     move: H.
     apply H0.
    +rewrite -(Complement_Complement U X).
     move => H0.
     move: H0.
     apply H.
  Qed.

  Lemma include_contrapositive:
    forall (X Y:Ensemble U), X ⊂ Y <-> (Y^c) ⊂ (X^c).
  Proof.
    move => X Y.
    rewrite /iff.
    split.
    +apply contrapositive.
     apply classic.
     move => H.
     unfold Included.
     move => H0.
     apply H.
     unfold Included.
     move => x.
     apply contrapositive.
     apply classic.
     rewrite -noone_in_complement.
     rewrite -noone_in_complement.
     apply H0.
    +unfold Included.
     move => H x.
     apply contrapositive.
     apply classic.
     rewrite noone_in_complement.
     rewrite (noone_in_complement x X).
     rewrite not_not_iff.
     rewrite not_not_iff.
     apply H.
     apply classic.
     apply classic.
  Qed.

End Class_Set_Theories.

Export class_set.
