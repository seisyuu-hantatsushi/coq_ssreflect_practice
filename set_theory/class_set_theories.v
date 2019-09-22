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

  Theorem union_assoc:
    forall (X Y Z:Ensemble U), (X ∪ Y) ∪ Z = X ∪ Y ∪ Z.
  Proof.
    move => X Y Z.
    apply /Extensionality_Ensembles.
    +split => x.
     apply.
     apply.
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

  Proposition double_setminus:
    forall (X Y:Ensemble U), X ⊂ Y -> Y \ (Y \ X) = X.
  Proof.
    move => X Y H.
    apply /Extensionality_Ensembles.
    split => a H'.
    inversion H'.
    apply NNPP.
    move => HF.
    apply H1.
    split.
    apply H0.
    done.
    split.
    apply H.
    apply H'.
    move => H0.
    inversion H0.
    apply H2.
    done.
  Qed.

  Lemma de_morgen_or_and_in_setminus:
    forall (A B X:Ensemble U),
      A ⊂ X /\ B ⊂ X ->
      X \ (A ∪ B) = (X \ A) ∩ (X \ B).
  Proof.
    move => A B X [HAX HBX].
    apply Extensionality_Ensembles.
    split => x H.
    inversion H.
    have L1: (~ x ∈ A) /\ (~ x ∈ B).
    split; move => H2;apply H1;[left|right];done.
    inversion L1.
    split;split;done.
    inversion H.
    inversion H0.
    inversion H1.
    split.
    apply H3.
    move => HF.
    inversion HF.
    apply H4.
    apply H7.
    apply H6.
    done.
  Qed.

End Class_Set_Theories.

Export class_set.
