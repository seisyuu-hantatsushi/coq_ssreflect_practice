From mathcomp Require Import ssreflect.

Require Import set_notations.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section UniqueExample.
  Variable U:Type.
  Import SetNotations.
  
  Goal forall (A B: Ensemble U),
      (exists! x, x ∈ A) ->
                  (forall (x:U),(x∈ A) -> (x ∈ B)) -> exists x, (x∈ A) /\ (x ∈ B).
  Proof.
    move => A B H H0.
    destruct H.
    unfold unique in H.
    exists x.
    inversion H.
    split.
    apply H1.
    apply H0.
    apply H1.
  Qed.

End UniqueExample.