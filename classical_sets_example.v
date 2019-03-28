From mathcomp Require Import ssreflect.
Require Import Classical_sets.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Classical_Sets_Examples.
  Variable U : Type.
  Notation "A ^c"   := (Complement U A) (at level 49).
  Notation "A ∪ B" := (Union U A B) (at level 50).
  Notation "A ∩ B" := (Intersection U A B) (at level 50).

  Theorem UnionComm:
    forall (A B: Ensemble U), A ∪ B = B ∪ A.
  Proof.
    move => A B.
    apply: Extensionality_Ensembles. (* Axiom of Extensionality of Sets *)
    split => x; case; move => y H1.
      by right.
      by left.
      by right.
      by left.
  Qed.

  Theorem IntersectionComm:
    forall (A B: Ensemble U), A ∩ B = B ∩ A.
  Proof.
    move => A B.
    apply: Extensionality_Ensembles.
    split => x; case => y H1 H2; apply /Intersection_intro.
    apply /H2.
    apply /H1.
    apply /H2.
    apply /H1.
  Qed.

  Theorem DeMorganLaw_Intersection:
    forall (A B: Ensemble U), (A ∩ B)^c = A^c ∪ B^c.
  Proof.
    move => A B.
    apply: Extensionality_Ensembles.
    split => x H1.
    -apply: NNPP.
     rewrite /not.
     move => H2.
     apply H1.
     apply /Intersection_intro.
     apply: NNPP.
     rewrite /not.
     move => H3.
     apply: H2.
     left.
     apply: H3.
     apply: NNPP.
     rewrite /not.
     move => H3.
     apply: H2.
     right.
     apply: H3.
    +move: H1.
     move => H1.
     move => H2.
     inversion H1.
     inversion H2.
     move: H3.
     apply H.
     inversion H2.
     move: H4.
     apply H.
  Qed.
End Classical_Sets_Examples.