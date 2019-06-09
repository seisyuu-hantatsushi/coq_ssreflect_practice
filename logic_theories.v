From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Coq.Logic.Decidable. (* Introducing decidable *)

Section Logic_Theories.
  Lemma or_dist_and: forall (A B C:Prop), A \/ (B /\ C) <-> (A \/ B) /\ (A \/ C).
  Proof.
    move => A B C.
    rewrite /iff.
    split.
    case.
    move => HA.
    split.
    left.
    apply HA.
    left.
    apply HA.
    case.
    move => HB HC.
    split; right.
    apply HB.
    apply HC.
    case.
    move => HAB HAC.
    inversion HAB.
    left.
    apply H.
    inversion HAC.
    left.
    apply H0.
    right.
    split.
    apply H.
    apply H0.
  Qed.

End Logic_Theories.
