From mathcomp Require Import all_ssreflect boolp classical_sets.

Section Classical_Sets_Examples.
  Local Open Scope classical_set_scope. 

  Variable T:Type.
  
  Inductive Fruits : Type :=
  | Apple
  | Orange
  | PineApple
  | Mango.

  Definition IsMyFruits (fruits : Fruits) : Prop :=
    match fruits with
    | Apple => True
    | Orange => True
    | Mango => True
    | _ => False
    end.

  Goal Apple \in mkset IsMyFruits.
    Show Proof.
    rewrite in_setE.
    rewrite mksetE.
    by [].
  Qed.

  Goal PineApple \in setT.
  Proof.
    rewrite in_setE.
    unfold setT.
    unfold mkset.
    reflexivity.
  Qed.

  Goal PineApple \in ~`mkset IsMyFruits.
  Proof.
    rewrite in_setE.
    unfold setC.
    unfold mkset.
    unfold IsMyFruits.
    move => HF.
      by [].
  Qed.

  Print Nat.even.
  
  Goal 2 \in mkset Nat.even.
  Proof.
    rewrite in_setE.
    unfold mkset.
    unfold Nat.even.
    rewrite trueE.
      by [].
  Qed.

  Goal 3 \notin mkset Nat.even.
  Proof.
    rewrite notin_set.
    unfold mkset.
    unfold Nat.even.
    move => HF.
    rewrite falseE in HF.
      by [].
  Qed.

  (* Commutative law of union. A ∪ B = B ∪ A *)
  Goal forall A B: set T, (A `|` B) = (B `|` A).
  Proof.
    move => A B.
    rewrite /setU. (* definition of union of set *)
    rewrite /mkset. (* definition of set *)
    rewrite predeqE => x. (* (A = B) = forall x, A x <-> B x) *)
    rewrite /iff. (* if and only if *)
    split;case => H. (* Divied cases *)
    right. trivial.
    left. trivial.
    right. trivial.
    left. trivial.
  Qed.

  (* setUC is Commutative law of union *)
  Goal forall A B: set T, (A `|` B) = (B `|` A).
  Proof.
    move => A B.
    apply setUC.
  Qed.

  Goal forall A B: set T, ~`(A `|` B) = ~`A `&` ~`B.
  Proof.
    move => A B.
    rewrite predeqE => x.
    apply: asbool_eq_equiv.
    rewrite asbool_and.
    rewrite !asbool_neg.
    rewrite asbool_or.
    rewrite negb_or.
    trivial.
  Qed.

  Goal forall A B: set T, ~`(A `|` B) = ~`A `&` ~`B.
  Proof.
    apply setCU.
  Qed.

  Goal forall A: set T, setM A set0 = set0 :> set (T * T).
  Proof.
    move => A.
    rewrite predeqE => -[x y].
    rewrite /iff.
    split => H.
    inversion H.
    apply H1.
    split.
    inversion H.
    apply H.
  Qed.

End.

