From mathcomp Require Import ssreflect.

Require Import img_example.
Require Import Coq.Sets.Relations_3_facts.

Section RelationExample.

Definition ID (U:Type): Relation U := fun x:U => fun y:U => x = y.
Definition ID' (U:Type): U -> U -> Prop := fun x:U => fun y:U => x = y.

Check (forall (U:Type) (x:U), (ID U x x)).

Check Equivalence.
Check ID.
Check ID'.

Check (forall (U:Type) (x:U), ID U x x).

Goal forall (U:Type), Equivalence U (ID U).
Proof.
  move => U.
  split.
  unfold Reflexive.
  move => x.
  unfold ID.
  reflexivity.
  unfold Transitive.
  move => x y z.
  unfold ID.
  move => H0 H1.
  rewrite H0.
  apply H1.
  unfold Symmetric.
  move => x y.
  unfold ID.
  move => H.
  rewrite H.
  reflexivity.
Qed.

Goal forall (U:Type), Equivalence U (ID' U).
Proof.
  move => U.
  split.
  unfold Reflexive.
  move => x.
  unfold ID'.
  reflexivity.
  unfold Transitive.
  move => x y z.
  unfold ID'.
  move => H0 H1.
  rewrite H0.
  apply H1.
  unfold Symmetric.
  move => x y.
  unfold ID'.
  move => H.
  rewrite H.
  reflexivity.
Qed.

End RelationExample.
