From mathcomp Require Import ssreflect.

(* Require Import powersets_notations. *)
Require Import set_notations.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Reference 1 [R1]:集合と位相 斎藤毅 ISBN 978-4-13-062958-4 *)
Section PowerSets_Example.

  Import SetNotations.

  Variable U:Type.
  Variable a b c: U.

  Definition P (X:Ensemble U) : (Ensemble (Ensemble U)) :=
    Power_set U X.

  Check P({| a, b |}).

  Goal {| {| a |}, {| a, b |} |} ⊂ P({| a, b |}).
  Proof.
    move => X H1.
    apply: Definition_of_Power_set.
    inversion H1.
    move => y H2.
    inversion H.
    left.
    move : H2.
    rewrite H3.
    apply.
    inversion H.
    move => y.
    apply.
  Qed.

  Goal {| {| a |}, {| b |}, {| a, b |}, {||} |} ⊂ P({| a, b |}).
  Proof.
    move => X H1.
    apply: Definition_of_Power_set.
    move: H1.
    case => Y.
    case => Z.
    case => W; case.
    rewrite /Included.
    move => x H1.
    left.
    apply H1.
    right.
    apply H.
    case.
    rewrite /Included => x.
    apply.
    case.
    rewrite /Included => x.
    case.
  Qed.

  (* R1 Problem A 1.3.2 *)
  Section Problem_A_1_3_2.
    Variable X C:Ensemble U.

    (* 
       I(A) := { C ∈ Power(X) | A ⊂ C }
       -> { C; Ensemble U | C ∈ Power(X) /\ A ⊂ C }
     *)
    Definition I (A:Ensemble U) : Ensemble (Ensemble U) :=
      {| C | fun C => In (Ensemble U) (Power_set U X) C /\ A ⊂ C |}.

    (* to comfirmi definition if I(A) *)
    Goal forall (A:Ensemble U), A ⊂ X -> I(A) ⊂ P(X).
    Proof.
      move => A H1.
      rewrite /Included /In => x.
      case => [C0 [HC0 HAC0]].
      split.
      move: HC0.
      case => Y.
      exact.
    Qed.

    Lemma LAinIA: forall (A:Ensemble U), A ⊂ X -> A ∈ I(A).
    Proof.
      -move => A H1.
       rewrite /In.
       split.
       split.
       split.
       exact H1.
       exact.
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
       move => C0.
       case => HPC0.
       exact.

      have LTS: forall (S T: Ensemble U), S ⊂ X /\ T ⊂ X -> I(S)=I(T) -> T ⊂ S.
      -move => S T.
       case => HS HT HIeq.
       move: (@LAinIA S).
       rewrite HIeq.
       case.
       apply HS.
       move => C0.
       case => HTC0.
       exact.

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
    Goal forall (A B :Ensemble U), A ⊂ X /\ B ⊂ X /\ C ⊂ X -> (C ∈ (I(A) ∩ I(B)) <-> A ⊂ C /\ B ⊂ C).
    Proof.
      move => A B.
      case => [HA [HB HC]].
      rewrite /iff.
      split.
      -case => [Y H1 H2].
       split.
       inversion H1.
       inversion H.
       apply H4.
       inversion H2.
       inversion H.
       apply H4.
      -case => HAC HBC.
       split.
       split.
       split.
       split.
       apply HC.
       apply HAC.
      -split.
       split.
       split.
       apply HC.
       apply HBC.
    Qed.

    (* (2) *)
    Goal forall (A B :Ensemble U), A ⊂ X /\ B ⊂ X -> (I(A ∪ B) = I(A) ∩ I(B)).
    Proof.
      move => A B.
      case => HA HB.
      apply: Extensionality_Ensembles.
      split => Z H.
      -split.
       --split; split.
         split.
         inversion H.
         inversion H0.
         inversion H2.
         apply H4.
         inversion H.
         inversion H0.
         inversion H2.
         move => y H6.
         rewrite /Included in H3.
         apply: (H3 y).
         left.
         exact H6.
       --split; split.
         split.
         inversion H.
         inversion H0.
         inversion H2.
         apply H4.
         inversion H.
         inversion H0.
         inversion H2.
         move => y H6.
         apply: (H3 y).
         right.
         exact H6.
      -split.
       --split.
         split.
         inversion H.
         inversion H0.
         inversion H3.
         inversion H5.
         apply H7.
       --move => x.
         inversion H.
         inversion H0.
         inversion H3.
         case => y.
         apply: (H6 y).
         inversion H1.
         inversion H7.
         apply: (H10 y).
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