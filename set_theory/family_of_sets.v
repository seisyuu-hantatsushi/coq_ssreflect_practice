From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import function.

(* IndexedFunction is functional formula *)
Definition IndexedFunction {U:Type} := U -> U.

Inductive IndexedSet {U:Type} (I:IndexedFunction) (i:U) : Ensemble U :=
| Definition_of_IndexedSet: forall(x:U), i = I x -> x ∈ IndexedSet I i.

Inductive IndexedSubset {U:Type} (I:IndexedFunction) (X:Ensemble U) (i:U) : Ensemble U :=
| Definition_of_IndexedSubset: forall(x:U), i = I x /\ x ∈ X -> x ∈ IndexedSubset I X i.

Inductive FamilyOfSets {U:Type} (X:U -> Ensemble U) (I:Ensemble U) :
  Ensemble (Ensemble U) :=
| Definition_of_FamilyOfSets: forall(i:U), i ∈ I -> (X i) ∈ FamilyOfSets X I.

Inductive UnionOfIndexedSets {U:Type} (X:U -> Ensemble U) (P:U -> Prop) : Ensemble U :=
 |Definition_of_UnionOfIndexedSets: forall(x:U), (exists i:U, P i /\ x ∈ (X i)) -> x ∈ UnionOfIndexedSets X P.

Inductive IntersectionOfIndexedSets {U:Type} (X:U -> Ensemble U) (I:Ensemble U) : Ensemble U :=
| Definition_of_IntersionOfIndexedSets: forall(x:U), (forall i:U, i ∈ I /\ x ∈ (X i)) -> x ∈ IntersectionOfIndexedSets X I.

(* ⋃ : Unicode 22C3 (N-ARY UNION) *)
(* ˍ : Unicode 02CD (MODIFIER LETTER LOW MACRON) *)
Notation "⋃ ˍ [ P ] X " := (UnionOfIndexedSets X P) (at level 45).
(* ⋂ : Unicode 22C2 (N-ARY INTERSECTION) *)
(* ˍ : Unicode 02CD (MODIFIER LETTER LOW MACRON) *)
Notation "⋂ ˍ [ P ] X " := (IntersectionOfIndexedSets X P) (at level 45).

Section FamilyOfSets.
  Variable U:Type.
  Variable I:Ensemble U.
  Variable IndexedF: U -> U.

  Definition Xn := IndexedSet IndexedF.

  Goal forall (i:U), i ∈ I -> Xn i ∈ FamilyOfSets Xn I.
  Proof.
    move => i H.
    split.
    apply H.
  Qed.

  Theorem union_of_family_of_sets: forall(I0 I1: Ensemble U),
      I = I0 ∪ I1 -> (⋃ ˍ [ fun(i:U) => i ∈ I ] Xn) = (⋃ ˍ [ fun(i:U) => i ∈ I0 ] Xn) ∪ (⋃ ˍ [ fun(i:U) => i ∈ I1 ] Xn).
  Proof.
    move => I0 I1 H.
    apply /Extensionality_Ensembles.
    split => x H0.
    -inversion H0.
     rewrite H in H1.
     inversion H1 as [i].
     inversion H3.
     inversion H4 as [i' H6 |i' H6]; [left|right]; split; exists i; split.
     +apply H6.
      apply H5.
     +apply H6.
      apply H5.
    -rewrite H.
     split.
     inversion H0; inversion H1; inversion H3 as [i']; inversion H5; exists i'; split.
     ++left.
       apply H6.
       apply H7.
     ++right.
       apply H6.
       apply H7.
  Qed.

End FamilyOfSets.
