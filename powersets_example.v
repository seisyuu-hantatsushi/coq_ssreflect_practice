From mathcomp Require Import ssreflect.

Require Import Powerset_Classical_facts.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Reference 1 [R1]:集合と位相 斎藤毅 ISBN 978-4-13-062958-4 *)

Section PowerSets_Example.
  Variable U V: Type.
  Notation "x ∈ X" := (In _ X x) (at level 48).
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

(*
  Variable X : Ensemble U.
  Inductive IP (A: Ensemble U) : Ensemble (Ensemble U) :=
    intro_IP: forall (C:Ensemble U), (A ⊂ X -> A ⊂ C -> In (Ensemble U) (Power_set U X) C) -> In (Ensemble U) (IP A) C.
  Check IP.

  Check Definition_of_Power_set.
  Definition_of_Power_set
     : forall (U : Type) (A X : Ensemble U), X ⊂ A -> X ∈ Power_set U A
  = { X ∈ Power(A) | X ⊂ A }

  I(A) = { C ∈ Power(X) | A ⊂ C }
  I(A) = { C ∈ { A ∈ Power(X) | A ⊂ X } | A ⊂ C }
   -> forall A C, A ⊂ C -> C ∈ { A ∈ Power(X) | A ⊂ X }
   -> forall A C, A ⊂ C -> C ∈ Power(X)
*)

  (* {C ∈ Power(X)| P(C)}, P(C)=A ⊂ C *)
  Inductive sigPE (X:Ensemble U) (P:Ensemble U -> Prop) :
      Ensemble (Ensemble U) :=
    Definition_of_Intensive_Power_set:
      forall C:Ensemble U, P C ->
                           (Included U C X -> In (Ensemble U) (sigPE X P) C).

  Variable X:Ensemble U.
  (* I(A) := {C ∈ Power(X) | A ⊂ C} *)
  Definition I (A:Ensemble U) : Ensemble (Ensemble U) :=
    sigPE X (fun c => A ⊂ c).

  Goal forall (A:Ensemble U), A ⊂ X -> I(A) ⊂ P(X).
  Proof.
    move => A H1.
    rewrite /Included /In => x.
    case => C HAC HCX.
    apply Definition_of_Power_set.
    done.
  Qed.

  Lemma L1: forall (A:Ensemble U), A ⊂ X -> A ∈ I(A).
  Proof.
    move => A H1.
    rewrite /In.
    apply Definition_of_Intensive_Power_set.
    done.
    exact H1.
  Qed.

  Lemma L2: forall (A B C:Ensemble U), A ⊂ B -> B ⊂ C -> A ⊂ C.
  Proof.
    move => A B C.
    move => HAB HBC.
    move => x HA.
    apply: (HBC x).
    apply: (HAB x).
    exact HA.
  Qed.

  Goal forall (A B :Ensemble U), A ⊂ X /\ B ⊂ X -> (A = B <-> I(A)=I(B)).
  Proof.
    move => A B.
    case => HA HB.
    rewrite /iff.
    split.
    move => Heq.
    rewrite -Heq.
    done.
    move => HIeq.
    move: (@L1 A) (@L1 B).
    case.
    apply HA.
    move => C HAC HCX.
    case.
    apply HB.
    move => C0.
  Abort.

  (* R1 Problem A 1.3.3 (1). X ⊂ Y <-> P(X) ⊂ P(Y) *)
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
