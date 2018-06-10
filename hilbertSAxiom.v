From mathcomp
     Require Import ssreflect.

Section ModusPonens.
  Variables X Y : Prop.

  Hypothesis XtoY_is_true : X -> Y.
  Hypothesis X_is_true : X.

  Theorem ModusPonens : Y.
  Proof.
    move: X_is_true. apply XtoY_is_true.
  Qed.
End ModusPonens.

Section HilbertSAxiom.
  Variables A B C : Prop.
  Theorem HS1:
    (A -> (B -> C)) -> ((A -> B) -> (A -> C)).
  Proof.
    move => AtoBtoC_is_true.
    move => AtoB_is_true.
    move => A_is_true.

    apply: (ModusPonens B C).
    apply: (ModusPonens A (B -> C)).
    by [].
    by [].

    apply: (ModusPonens A B).
    by [].
    by [].
  Qed.
End HilbertSAxiom.