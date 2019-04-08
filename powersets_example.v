From mathcomp Require Import ssreflect.

Require Import Powerset_Classical_facts.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section PowerSets_Example.
  Variable U V: Type.
  Notation "A ⊂ B" := (Included U A B) (at level 48).
  Notation "A ^c"   := (Complement U A) (at level 49).
  Notation "A ∪ B" := (Union U A B) (at level 50).
  Notation "A ∩ B" := (Intersection U A B) (at level 50).
  Notation "A \ B" := (Setminus U A B) (at level 50).

  Goal forall (X :Ensemble U), In (Ensemble U) (Power_set U X) X.
    move => X.
    rewrite /In.
    apply Definition_of_Power_set.
    done.
  Qed.
  
  Theorem A_1_3_3_1:
    forall (X Y:Ensemble U), X ⊂ Y -> Included (Ensemble U) (Power_set U X) (Power_set U Y).
  Proof.
    move => X Y.
    rewrite /Included.
    move => H1 Px.
    rewrite /In.
    case => Py.
    rewrite /Included => H2.
    apply Definition_of_Power_set.
    rewrite /Included.
    move => u H3.
    apply : (H1 u).
    apply : (H2 u).
    apply H3.
  Qed.
  
End PowerSets_Example.