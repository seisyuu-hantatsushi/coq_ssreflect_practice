From mathcomp Require Import ssreflect.

Require Import powersets_notations.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import PowersetNotations.

Module DirectProductNotations.

  Definition OrderedPair (U:Type) (a b : U) := {|{|a|},{|a,b|}|}.

  Inductive DirectProduct (U:Type) (X Y:Ensemble U) : Ensemble (Ensemble (Ensemble U)) :=
    Definition_of_DirectProduct:
      forall (Z: Ensemble (Ensemble U)),
        (exists x:U, exists y:U, (x ∈ X /\ y ∈ Y /\ Z = {|{|x|},{|x,y|}|})) ->
        In (Ensemble (Ensemble U)) (DirectProduct X Y) Z.

  Notation "X × Y" := (@DirectProduct _ X Y) (at level 49).
  Notation "(| a , b |)" := (@OrderedPair _ a b) (at level 48).

End DirectProductNotations.

(* Reference 1 [R1]:集合と位相 斎藤毅      ISBN 978-4-13-062958-4 *)
(* Reference 2 [R2]:数学の基礎 島内剛一                           *)
Section PairExamples.
  Variable U:Type.
  Variable a b c: U.

  Import DirectProductNotations.

  (* R1 定義 1.3.1 *)
  (* R2 P.82-83 直積 *)
  Goal forall (x y:U) (A B:Ensemble U), (x ∈ A /\ y ∈ B) -> OrderedPair x y ∈ Power_set (Ensemble U) (Power_set U (A ∪ B)).
  Proof.
    move => x y A B.
    case => [HA HB].
    rewrite /OrderedPair.
    split.
    move => X.
    move => H1.
    split.
    move => z.
    inversion H1.
    inversion H.
    case.
    left.
    apply HA.
    inversion H1.
    inversion H.
    case; move => w.
    case.
    left.
    apply HA.
    case.
    right.
    apply HB.
    inversion H2.
    case; move => w.
    case.
    left.
    apply HA.
    case.
    right.
    apply HB.
  Qed.

  Goal forall (X Y A B: Ensemble U) (x y:U), (x ∈ A) /\ (y ∈ B) /\ A ⊂ X /\ B ⊂ Y -> (A × B) ⊂ (X × Y).
  Proof.
    move => X Y A B x y.
    case => [Hx [Hy [HA HB Z]]].
    move => H.
    inversion H.
    inversion H0.
    inversion H2.
    inversion H3.
    inversion H5.
    rewrite H7.
    apply Definition_of_DirectProduct.
    exists x0.
    exists x1.
    split.
    move: H4.
    apply HA.
    split.
    move: H6.
    apply HB.
    reflexivity.
  Qed.

  Check (| a , b |).
  Goal forall (X Y:Ensemble U), a ∈ X /\ b ∈ Y -> (| a, b |) = { (X ∪ Y) |^ (fun A => {|a|} ⊂ A /\ A ⊂ {|a, b|} ) }.
  Proof.
    move => X Y.
    case => [Ha Hb].
    apply Extensionality_Ensembles.
    split => W.
    move => H1.
    apply Definition_of_Intensive_Power_set.
    inversion H1.
    split.
    move => w.
    inversion H.
    apply.
    move => z H2.
    inversion H.
    left.
    move: H2.
    rewrite H3.
    apply.
    split.
    inversion H.
    move => z H3.
    left.
    apply H3.
    inversion H.
    move => z.
    apply.
    
    inversion H1.
    inversion H.
    move => w.
    case.
    left.
    apply Ha.

    inversion H.
    move => w.
    case => z; case.
    left.
    apply Ha.
    right.
    apply Hb.

    (**)
    case.
    move => C.
    move => H1 H2.
    rewrite /OrderedPair.
  Abort
End PairExamples.