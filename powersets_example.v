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

  Goal forall (X :Ensemble U), X ∈ P(X).
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

  Notation "{ X |^ P }" := (sigPE X P).

  (* R1 Problem A 1.2.1.1 *)
  Lemma LSubset_1:
    forall (A B C X:Ensemble U), A ⊂ X /\ B ⊂ X /\ C ⊂ X -> ((A ∪ B) ⊂ C <-> A ⊂ C /\ B ⊂ C).
  Proof.
    move => A B C X H0.
    rewrite /iff.
    split.
    -move => H1.
     split; move :H1 => H1 x H2; apply H1.
     left.
     apply H2.
     right.
     apply H2.
    -case => HAC HBC x.
     case => x1.
     apply HAC.
     apply HBC.
  Qed.

  (* R1 Problem A 1.2.1.2 *)
  Lemma LSubset_2:
    forall (A B C:Ensemble U), (C ⊂ A \/ C ⊂ B ->  C ⊂ (A ∪ B)).
  Proof.
    move => A B C.
    case => H1.
    left.
    move: H.
    apply: H1.
    right.
    move: H.
    apply: H1.
  Qed.

  (* R1 Problem A 1.3.2 *)
  Section Problem_A_1_3_2.
    Variable X:Ensemble U.

    (* I(A) := {C ∈ Power(X) | A ⊂ C} *)
    Definition I (A:Ensemble U) : Ensemble (Ensemble U) :=
      { X |^ (fun C => A ⊂ C) }.

    (* to comfirmi definition if I(A) *)
    Goal forall (A:Ensemble U), A ⊂ X -> I(A) ⊂ P(X).
    Proof.
      move => A H1.
      rewrite /Included /In => x.
      case => C HAC HCX.
      apply Definition_of_Power_set.
      done.
    Qed.

    Lemma LAinIA: forall (A:Ensemble U), A ⊂ X -> A ∈ I(A).
    Proof.
      -move => A H1.
       rewrite /In.
       apply Definition_of_Intensive_Power_set.
       done.
       exact H1.
    Qed.

    (* (1) *)
    Goal forall (A B :Ensemble U), A ⊂ X /\ B ⊂ X -> (A = B <-> I(A)=I(B)).
    Proof.
      move => A B.
      case => HA HB.
      rewrite /iff.
      split.
      move => Heq.
      rewrite -Heq.
      done.

      have LST: forall (S T: Ensemble U), S ⊂ X /\ T ⊂ X -> I(S)=I(T) -> S ⊂ T.
      -move => S T.
       case => HS HT HIeq.
       move: (@LAinIA T).
       rewrite -HIeq.
       case.
       apply HT.
       move => C HSC HCX.
       exact HSC.

     have LTS: forall (S T: Ensemble U), S ⊂ X /\ T ⊂ X -> I(S)=I(T) -> T ⊂ S.
      -move => S T.
       case => HS HT HIeq.
       move: (@LAinIA S).
       rewrite HIeq.
       case.
       apply HS.
       move => C HTC HCX.
       exact HTC.

     (* main Prop *)
     move => HIeq.
     apply: Extensionality_Ensembles.
     split.
     apply LST.
     split.
     exact HA.
     exact HB.
     exact HIeq.
     apply LTS.
     split.
     exact HA.
     exact HB.
     exact HIeq.
    Qed.

    (* (2) *)
    Goal forall (A B :Ensemble U), A ⊂ X /\ B ⊂ X -> (I(A ∪ B) = I(A) ∩ I(B)).
    Proof.
      move => A B.
      case => HA HB.
      apply: Extensionality_Ensembles.
      split.
      -move => x.
       case => C.
       rewrite /Included.
       move => H1 H2.
       split;
         apply Definition_of_Intensive_Power_set;
         move => x0;
         move: (H1 x0);
         move => H3 H4.
       apply H3.
       left.
       apply H4.
       apply (H2 x0).
       apply H4.
       apply H3.
       right.
       apply H4.
       apply (H2 x0).
       apply H4.
      -move => D H1.
       apply Definition_of_Intensive_Power_set.
       inversion H1.
       move => x1.
       case => x2 H3.
       move: H.
       case => C HAC HCX.
       move: H3.
       apply HAC.
       move: H0.
       case => C HBC HCX.
       move: H3.
       apply HBC.
       move: H1.
       case => E H1.
       case => C.
       done.
    Qed.

    Lemma L1: forall (A C:Ensemble U), C ∈ P(X) -> C ∈ I(A) <-> A ⊂ C.
    Proof.
      move => A C HPC.
      rewrite /iff.
      split.
      -case => C0.
       done.
       move => HAC.
       apply Definition_of_Intensive_Power_set.
       done.
       move: HPC.
       case.
       done.
    Qed.

    Lemma L1Union: forall (A B C:Ensemble U), C ∈ P(X) -> C ∈ I(A ∪ B) <-> (A ∪ B) ⊂ C.
    Proof.
      move => A B C.
      move:  (@L1 (A ∪ B) C).
      done.
    Qed.

    Lemma L2: forall (A B C:Ensemble U), C ∈ P(X) -> C ∈ (I(A) ∩ I(B)) <-> A ⊂ C /\ B ⊂ C.
    Proof.
      move => A B C PX.
      rewrite /iff.
      -split.
       +split; move: H; case; move => x HIA HIB.
        move: HIA.
        case.
        done.
        move: HIB.
        case.
        done.
      -case => HAC HBC.
       split; apply Definition_of_Intensive_Power_set.
       +apply HAC.
        move: PX.
        case.
        done.
       +apply HBC.
        move: PX.
        case.
        done.
    Qed.

    (* (2) *)
    Goal forall (A B:Ensemble U), A ⊂ X /\ B ⊂ X -> (I(A ∪ B) = I(A) ∩ I(B)).
    Proof.
      move => A B.
      case => HA HB.
      apply: Extensionality_Ensembles.
      split.
      -move => C H1.
       inversion H1.
       rewrite L2.
       move: H1.
       rewrite L1Union.
       apply (@LSubset_1 A B C X).
       split.
       apply HA.
       split.
       apply HB.
       apply H0.
       apply: Definition_of_Power_set.
       done.
      -apply: Definition_of_Power_set.
       apply: H0.
       move => C H1.
       inversion H1.
       rewrite L1Union.
       move: H1.
       rewrite L2.
       apply (@LSubset_1 A B C X).
       split.
       apply HA.
       split.
       apply HB.
       move : H.
       case => C0.
       done.
       apply: Definition_of_Power_set.
       move : H.
       case.
       done.
       apply: Definition_of_Power_set.
       move : H.
       case.
       done.
    Qed.
  End Problem_A_1_3_2.

  (* R1 Problem A 1.3.3 (1). X ⊂ Y <-> P(X) ⊂ P(Y) *)
  Goal forall (X Y:Ensemble U), X ⊂ Y <-> (P(X)) ⊂ (P(Y)).
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
