From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Coq.Logic.Classical.
Require Import Coq.Logic.Decidable.

Section Logic_Pred_Theories.
  Variable U:Type.
  Variable C:Prop.
  Variable a:U.

  Lemma forall_bound_variable_and_out:
    forall (A:U->Prop), (C /\ forall (x:U), A x) <-> forall (x:U), C /\ A x.
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
    suff: C /\ A a.
    case => HC HA.
    split.
    apply HC.
    apply H.
    apply H.
  Qed.

  Check forall_bound_variable_and_out.
  About forall_bound_variable_and_out.

  Lemma forall_bound_variable_or_out:
    forall (A:U->Prop), (C \/ forall (x:U), A x) <-> (forall (x:U), C \/ A x).
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

apply    Logic_Pred_Theories.