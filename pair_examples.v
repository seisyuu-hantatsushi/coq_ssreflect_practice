From mathcomp Require Import ssreflect.

Require Import set_notations.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module DirectProductNotations.

  Import SetNotations.
  Export SetNotations.

  Definition OrderedPair (U:Type) (a b : U) := {|{|a|},{|a,b|}|}.

  Inductive DirectProduct (U:Type) (X Y:Ensemble U) : Ensemble (Ensemble (Ensemble U)) :=
    Definition_of_DirectProduct:
      forall (Z: Ensemble (Ensemble U)),
        (exists x:U, exists y:U, (x ∈ X /\ y ∈ Y /\ Z = {|{|x|},{|x,y|}|})) ->
        In (Ensemble (Ensemble U)) (DirectProduct X Y) Z.

  Notation "𝒫( X )" := (@Power_set _ X) (at level 47).

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
  Goal forall (x y:U) (A B:Ensemble U), (x ∈ A /\ y ∈ B) -> OrderedPair x y ∈ 𝒫(𝒫(A ∪ B)).
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
    split.
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
  (*
    { A ∈ P(X ∪ Y) | {a} ⊂ A ⊂ {a, b} }
    -> { A | A ∈ P(X ∪ Y) /\ {a} ⊂ A /\ A ⊂ {a, b} }
  *)
  
  Goal forall (X Y A:Ensemble U), a ∈ X /\ b ∈ Y -> (| a, b |) ⊂ {| A | fun A => A ∈ 𝒫(X ∪ Y) /\ {|a|} ⊂ A /\ A ⊂ {|a, b|} |}.
  Proof.
    move => X Y A.
    case => [Ha Hb Z].
    -case => W.
     --case.
       split.
       split.
       split => x.
       case.
       left.
       exact.
     --split.
       exact.
     --left.
       exact.
    -case.
     split.
     --split.
       split => x.
       case => y; case.
       ---left.
          exact.
       ---right.
          exact.
     --split => x.
       left.
       exact.
       exact.
  Qed.

  Goal forall (x:U) (X z:Ensemble U), (a ∈ X /\ b ∈ X /\ x ∈ X /\ z ∈ (| a, b |)) -> ( x = a <-> x ∈ z ). 
  Proof.
    move => x X z.
    case => [H1 [H2 [H3 H4]]].
    rewrite /iff.
    split.
    -move => Hax.
     rewrite Hax.
     inversion H4.
     inversion H.
     reflexivity.
     inversion H.
     left.
     reflexivity.
     inversion H4.
     inversion H.
     case.
     reflexivity.
     move => H6.
     move : H.
     case.
     apply Singleton_inv.
     
End PairExamples.