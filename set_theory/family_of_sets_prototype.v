From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import function.

Inductive SetOfSingleton {U:Type} (M:Ensemble U) : Ensemble (Ensemble U) :=
| Definition_of_SetOfSingleton: forall (a:U), a ∈ M -> {|a|} ∈ SetOfSingleton M.

Section FamilyOfSetsPrototype.
  Variable U:Type.
  Variables X Y I:Ensemble U.

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

  Goal forall (i:U)
              (II X:Ensemble (Ensemble U))
              (Xn:Ensemble (Ensemble (Ensemble (Ensemble U))))
              (F:FunctionOfMap (Ensemble U)),
      i ∈ I /\ II=SetOfSingleton I /\ Xn ≔ F ⊦ II ⟼ X -> exists! Xi, {|Xi|} = Xn '' {|{|i|}|}.
  Proof.
    move => i II X0 Xn F [HiI [HII [HXn HXnS]]].
    have L1: exists Xi:Ensemble U, (|{|i|},Xi|) ∈ Xn.
    apply (HXnS {|i|}).
    rewrite HII.
    split.
    done.
    inversion L1 as [Xi].
    exists Xi.
    split.
    apply /Extensionality_Ensembles.
    split => X' H0.
    split.
    exists {|i|}.
    split.
    done.
    apply singleton_eq_iff in H0.
    rewrite H0.
    done.
    rewrite HXn in H.
    inversion H as [I' X0'].
    inversion H0 as [X1' [I1' []]].
    apply singleton_eq_iff in H3.
    rewrite H3 in H4.
    rewrite HXn in H4.
    inversion H4 as [I2' X2' []].
    inversion H1.
    apply ordered_pair_iff in H2.
    inversion H2.
    apply ordered_pair_iff in H8.
    inversion H8.
    rewrite H14 in H6.
    rewrite H13 in H6.
    rewrite H12 in H9.
    rewrite H11 in H9.
    rewrite -H9 in H6.
    apply singleton_eq_iff.
    done.
    move => Xi' H0.
    apply Extension in H0.
    inversion H0.
    apply singleton_eq_iff.
    apply (H2 Xi).
    split.
    exists {|i|}.
    split.
    done.
    apply H.
  Qed.
  
End FamilyOfSetsPrototype.
