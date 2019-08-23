From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import function.

Inductive SetOfSingleton {U:Type} (M:Ensemble U) : Ensemble (Ensemble U) :=
| Definition_of_SetOfSingleton: forall (a:U), a ∈ M -> {|a|} ∈ SetOfSingleton M.

Section FamilyOfSetsPrototype.
  Variable U:Type.
  Variables X Y:Ensemble U.

  Lemma element_of_set_of_singleton_is_unique:
    forall (A X: Ensemble U) (a b:U),
      A ∈ SetOfSingleton X -> (a ∈ A /\ b ∈ A -> a = b).
  Proof.
    move => A X' a b H  [Ha Hb].
    inversion H.
    rewrite -H1 in Ha.
    rewrite -H1 in Hb.
    apply singleton_eq_iff in Ha.
    apply singleton_eq_iff in Hb.
    rewrite Ha Hb.
    done.
  Qed.

  Lemma set_of_singleton_cast:
    forall (z:U) (Z:Ensemble U), {|z|} ∈ SetOfSingleton Z <-> z ∈ Z.
  Proof.
    move => z Z.
    rewrite /iff.
    split => H.
    inversion H.
    apply (eq_singleton_eq_element_iff a z) in H0.
    rewrite -H0.
    apply H1.
    split.
    apply H.
  Qed.

  Lemma set_of_singlton_source_set_iff:
    SetOfSingleton X = SetOfSingleton Y <-> X = Y.
  Proof.
    rewrite /iff.
    split => H.
    apply Extension in H.
    inversion H as [HSX HSY].
    apply /Extensionality_Ensembles.
    split => z;rewrite -(set_of_singleton_cast z Y) -(set_of_singleton_cast z X).
    apply HSX.
    apply HSY.
    rewrite H.
    reflexivity.
  Qed.

End FamilyOfSetsPrototype.
