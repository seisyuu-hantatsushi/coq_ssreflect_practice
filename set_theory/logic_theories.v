From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Coq.Logic.Classical.
Require Import Coq.Logic.Decidable. (* Introducing decidable *)

Section Logic_Theories.
  Lemma or_dist_and: forall (A B C:Prop), A \/ (B /\ C) <-> (A \/ B) /\ (A \/ C).
  Proof.
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

  Lemma and_dist_or: forall (A B C:Prop), A /\ (B \/ C) <-> (A /\ B) \/ (A /\ C).
  Proof.
    rewrite /iff.
    split.
    case => HA.
    case => HB.
    left.
    split; done.
    right.
    split; done.
    case.
    case => HA HB.
    split.
    done.
    left.
    done.
    case => HA HC.
    split.
    done.
    right.
    done.
  Qed.

  Lemma or_imply_to_imply_and:
    forall (A B C:Prop), (A \/ B -> C) -> ((A -> C) /\ (B -> C)).
  Proof.
    move => A B C H.
    split; move => H0; apply H.
    left.
    apply H0.
    right.
    apply H0.
  Qed.

  Lemma or_not_l_iff_3: forall (A B C:Prop), (A -> False) \/ (B -> False) \/ C <-> (A /\ B -> C).
  Proof.
    move => A B C.
    rewrite /iff.
    split => H.
    case.
    move => HA.
    apply or_not_l_iff_2.
    apply classic.
    move: HA.
    apply or_not_l_iff_2.
    apply classic.
    apply H.
    apply or_not_l_iff_2.
    apply classic.
    move => HA.
    apply or_not_l_iff_2.
    apply classic.
    move => HB.
    apply H.
    split.
    apply HA.
    apply HB.
  Qed.

  Lemma imply_and_to_or_imply: forall (A B C:Prop), (A -> B /\ C) -> (A -> B) /\ (A -> C).
  Proof.
    move => A B C H.
    split; apply H.
  Qed.

End Logic_Theories.
