From mathcomp
     Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Ensembles.
Require Import Classical.

Section Ensembles_Practice.
  Variable U : Type.
  Lemma cc_cancel:
    forall A:Ensemble U, Complement U (Complement U A) = A.
  Proof.
    move => A.
    apply: Extensionality_Ensembles.
    rewrite /Complement /Same_set.
    split.
    rewrite /Included /In.
    move => x.
    apply: NNPP.
    rewrite /Included /In.
    move => x H1.
    rewrite /not.
    case.
    apply H1.
  Qed.