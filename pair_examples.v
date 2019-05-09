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

  Theorem DirectProduct_Product_Empty: forall (X:Ensemble U), X × {||} = {||}.
  Proof.
    move => X.
    apply /Extensionality_Ensembles.
    split => Y.
    -case.
     move => Z.
     case => x.
     case => y.
     case => [H1 [H2 H3]].
     rewrite H3.
     apply NNPP.
     rewrite /not => H4.
     move: H2.
     apply Noone_in_empty.
    -move => H0.
     apply NNPP.
     rewrite /not => H1.
     move: H0.
     apply Noone_in_empty.
  Qed.

  Theorem DirectProduct_Product_Empty_Comm: forall (X:Ensemble U), X × {||} = {||} × X.
  Proof.
    move => X.
    apply /Extensionality_Ensembles.
    split => Y; rewrite DirectProduct_Product_Empty.
    -move => H0.
     apply NNPP.
     rewrite /not => H1.
     move : H0.
     apply Noone_in_empty.
    -case => Z.
     case => x.
     case => y.
     case => [H0 [H1 H2]].
     apply NNPP.
     rewrite /not => H3.
     move: H0.
     apply Noone_in_empty.
  Qed.

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

  Theorem DirectProductDistCup :
    forall (A B C: Ensemble U), A × (B ∪ C) = A × B ∪ A × C.
  Proof.
    move => A B C.
    apply /Extensionality_Ensembles.
    split => X.
    -case => Z.
     case => x.
     case => y.
     case => [HA [HBC H0]].
     inversion HBC.
    --left.
      split.
      exists x.
      exists y.
      split.
      apply HA.
      split.
      apply H.
      apply H0.
    --right.
      split.
      exists x.
      exists y.
      split.
      apply HA.
      split.
      apply H.
      apply H0.
    -case => Y.
     --case => Z.
       case => x.
       case => y.
       case => [HA [HB HZ]].
       split.
       exists x.
       exists y.
       split.
       apply HA.
       split.
       left.
       apply HB.
       apply HZ.
     --case => Z.
       case => x.
       case => y.
       case => [HA [HC HZ]].
       split.
       exists x.
       exists y.
       split.
       apply HA.
       split.
       right.
       apply HC.
       apply HZ.
  Qed.

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

  Goal forall (X Y A:Ensemble U), a ∈ X /\ b ∈ Y -> {| A | fun A => A ∈ 𝒫(X ∪ Y) /\ {|a|} ⊂ A /\ A ⊂ {|a, b|} |} ⊂ (| a, b |).
  Proof.
    move => X Y A.
    case => HaX HbY Z.
    case => W.
    case => HP.
    case => Ha Hab.
    move: HP.
    case.
    move => S.
    rewrite /OrderedPair.
    move => HS.
    left.
    rewrite /Included in HS.
    move: (HS a) => HSa.
    rewrite /Included in Ha.
    rewrite /In.
    have L1: S = {|a|}.
    apply /Extensionality_Ensembles.
    split => x.
  Abort.

  (* R1 A 1.3.4 2 *)
  Goal forall (x:U) (X Y:Ensemble U), (a ∈ X /\ b ∈ Y /\ x ∈ X) -> ( x = a <-> forall (z:Ensemble U), (z ∈ (| a, b |)) -> x ∈ z ).
  Proof.
    move => x X Y.
    case => [HaX [HbY HxX]].
    rewrite /iff.
    split.
    -move => Hax z.
     rewrite Hax.
     case => y.
     case.
     reflexivity.
     case.
     left.
     reflexivity.
    -move => H1.
     apply eq_sym.
     apply Singleton_inv.
     apply (H1 {|a|}).
     left.
     split.
  Qed.

End PairExamples.
