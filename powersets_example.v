From mathcomp Require Import ssreflect.

Require Import Powerset_Classical_facts.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section PowerSets_Example.
  Variable U V: Type.
  Notation "A ⊂ B" := (Included _ A B) (at level 48).
  Notation "A ^c"   := (Complement _ A) (at level 49).
  Notation "A ∪ B" := (Union _ A B) (at level 50).
  Notation "A ∩ B" := (Intersection _ A B) (at level 50).
  Notation "A \ B" := (Setminus _ A B) (at level 50).

  Definition P (X:Ensemble U) : (Ensemble (Ensemble U)) :=
    Power_set U X.

  Goal forall (X :Ensemble U), In (Ensemble U) (Power_set U X) X.
    move => X.
    rewrite /In.
    apply Definition_of_Power_set.
    done.
  Qed.

  (* X ⊂ Y <-> P(X) ⊂ P(Y) *)
  Theorem A_1_3_3_1:
    forall (X Y:Ensemble U), X ⊂ Y <-> (P(X)) ⊂ (P(Y)).
  Proof.
    move => X Y.
    rewrite /Included /iff.
    split.
    +move => H1 Px.
     rewrite /In.
     case => Py.
     rewrite /Included => H2.
     apply: Definition_of_Power_set.
     move => u H3.
     apply : (H1 u).
     apply : (H2 u).
     exact H3.
    -rewrite /In.
     move => H1 x.
     move : (H1 X).
     case.
     apply: Definition_of_Power_set.
     done.
     move => x0.
     rewrite /Included => H2.
     exact (H2 x). 
  Qed.

End PowerSets_Example.
