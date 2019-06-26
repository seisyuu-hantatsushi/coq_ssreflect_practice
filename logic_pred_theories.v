From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Coq.Logic.Classical.
Require Import Coq.Logic.Decidable.

Section Logic_Pred_Theories.
  Variable U:Type.
  Variable a0:U.

  Lemma forall_bound_variable_and_dist_iff:
    forall (A B:U->Prop), ((forall (x:U), A x) /\ (forall (x:U), B x)) <-> forall (x:U), A x /\ B x.
  Proof.
    move => A B.
    rewrite /iff.
    split.
    (* forall (A B:U->Prop), ((forall (x:U), A x) /\ (forall (x:U), B x)) -> forall (x:U), A x /\ B x. *)
    move => H x.
    split.
    inversion H.
    apply H0.
    inversion H.
    apply H1.
    (* forall (A B:U->Prop), (forall (x:U), A x /\ B x) -> (forall (x:U), A x /\ forall (x:U), B x). *)
    move => H.
    split; apply H.
  Qed.

  Lemma forall_bound_variable_or_dist:
    forall (A B:U->Prop), (forall (x:U), A x) \/ (forall (x:U), B x) -> forall (x:U), A x \/ B x.
  Proof.
    move => A B H x.
    inversion H.
    left.
    apply H0.
    right.
    apply H0.
  Qed.

  Lemma forall_bound_variable_and_out:
    forall (A:U->Prop) (C:Prop), (C /\ forall (x:U), A x) <-> forall (x:U), C /\ A x.
  Proof.
    move => A.
    rewrite /iff.
    split.
    case => HC.
    move => HA x.
    split.
    apply HC.
    apply HA.
    move => H.
    suff: C /\ A a0.
    case => HC HA.
    split.
    apply HC.
    apply H.
    apply H.
  Qed.

  Lemma forall_bound_variable_or_out:
    forall (A:U->Prop) (C:Prop), (C \/ forall (x:U), A x) <-> (forall (x:U), C \/ A x).
  Proof.
    move => A.
    rewrite /iff.
    split.
    (* (C \/ forall (x:U), A x) -> (forall (x:U), C \/ A x) *)
    case.
    move => HC x.
    left.
    apply HC.
    move => H x.
    right.
    apply H.
    (* (forall (x:U), C \/ A x) -> (C \/ forall (x:U), A x)  *)
    move => H.
    apply imp_not_l.
    apply classic.
    move => H0.
    move => x.
    move: H0.
    apply imp_not_l.
    apply classic.
    apply H.
  Qed.

  Lemma forall_bound_variable_and_out_2:
    forall (A B:U->Prop), ((forall (x:U), A x) /\ (forall (y:U), B y)) <-> (forall (x y:U), A x /\ B y).
  Proof.
    +move => A B.
     rewrite /iff.
     split.
     ++case => HA HB x y.
       split.
       apply HA.
       apply HB.
     ++move => H.
       split.
       move => x.
       apply H.
       apply x.
       move => y.
       apply H.
       apply y.
  Qed.

  Lemma forall_bound_or_dist_2:
    forall (A B:U -> Prop), (forall (t s:U), ((A t) \/ (B s))) -> (forall (t:U), (A t)) \/ (forall (s:U), (B s)).
  Proof.
    move => A B H.
    apply imp_not_l.
    apply classic.
    move => H0 s.
    move: H0.
    apply imp_not_l.
    apply classic.
    apply or_comm.
    apply forall_bound_variable_or_out.
    move => t.
    apply or_comm.
    apply H.
  Qed.

End Logic_Pred_Theories.
