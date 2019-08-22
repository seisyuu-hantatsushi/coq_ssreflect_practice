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

  Goal forall (x:U), {|x|} ∈ SetOfSingleton X <-> x ∈ X.
  Proof.
    move => x.
    rewrite /iff.
    split => H.
    inversion H.
    apply (eq_singleton_eq_element_iff a x) in H0.
    rewrite -H0.
    apply H1.
    split.
    apply H.
  Qed.

End FamilyOfSetsPrototype.