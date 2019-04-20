From mathcomp Require Import ssreflect.

Require Import powersets_notations.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Reference 1 [R1]:集合と位相 斎藤毅 ISBN 978-4-13-062958-4 *)
Section PowerSets_Example.

  Import PowersetNotations.

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
       case => C HBC HCX.
       apply HCX.
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