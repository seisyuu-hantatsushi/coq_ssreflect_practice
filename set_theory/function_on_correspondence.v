From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import class_set.
Require Import direct_product_theories.
Require Import correspondence.

Definition FunctionOfMap (U:Type) := U -> U.

Definition Mapping {U:Type} (f:Ensemble (Ensemble (Ensemble U))) (A B: Ensemble U) :=
  f ⊂ A × B /\ forall (x:U), x ∈ A -> exists! y:U, (|x, y|) ∈ f.

Definition MappingWithFunction {U:Type} (f:Ensemble (Ensemble (Ensemble U))) (F:FunctionOfMap U) (A B: Ensemble U) :=
  f = (GraphOfBinaryRelation (fun (x y:U) => y = F x) A B) /\ forall (x:U), x ∈ A -> exists y:U, (|x, y|) ∈ f.

(* ≔ : Unicode 2254 (COLON EQUAL) *)
(* ⊦ : Unicode 22A6 (ASSERTION) *)
(* ⟼: Unicode:27FC (LONG RIGHTWARDS ARROW FROM BAR) *)

Notation "f ≔ F ⊦ A ⟼ B" := (MappingWithFunction f F A B) (at level 43).

Section FunctionDefinition.

  Variable U:Type.
  Variable F: FunctionOfMap U.
  Variable X Y:Ensemble U.

  Goal forall (f:Ensemble (Ensemble (Ensemble U))),
      f ≔ F ⊦ X ⟼ Y -> Mapping f X Y.
  Proof.
    move => f [Hf HfS].
    split.
    +apply (graph_is_included_in_direct_product Hf).
     move => x Hx.
     move: (HfS x).
     case.
     apply Hx.
     move => y H.
     exists y.
     split.
     apply H.
    +move => y' H'.
     rewrite Hf in H.
     rewrite Hf in H'.
     inversion H.
     inversion H1.
     apply ordered_pair_iff in H0.
     inversion H0.
     inversion H'.
     inversion H7.
     apply ordered_pair_iff in H6.
     inversion H6.
     rewrite H5 in H2.
     rewrite H4 in H2.
     rewrite H11 in H8.
     rewrite H10 in H8.
     rewrite H2 H8.
     reflexivity.
  Qed.

  Goal forall (f:Ensemble (Ensemble (Ensemble U))),
      (f ≔ F ⊦ X ⟼ Y) -> forall (x:U), x ∈ 𝕯( f ) -> exists! y, {|y|} = f '' {|x|}.
  Proof.
    move => f [Hf HfS] x HxDf.
    case: (HfS x).
    +inversion HxDf.
     inversion H.
     inversion H1 as [y].
     rewrite Hf in H3.
     inversion H3.
     inversion H5.
     rewrite H4 in H7.
     apply ordered_pair_in_direct_product_iff_and in H7.
     inversion H7.
     apply H8.
    +move => y H.
     inversion HxDf as [x' []].
     exists y.
     split.
     apply /Extensionality_Ensembles.
     -split => y0 H2.
      split.
      --inversion H0 as [y1].
        exists x.
        split.
        apply singleton_eq_iff.
        reflexivity.
      --apply singleton_eq_iff in H2.
        rewrite H2.
        apply H.
        inversion H2 as [y1 [x1 []]].
        rewrite Hf in H4.
        inversion H4.
        inversion H7.
        rewrite Hf in H.
        inversion H as [x3 y3 []].
        apply singleton_eq_iff in H3.
        apply ordered_pair_iff in H6.
        inversion H6.
        apply ordered_pair_iff in H12.
        inversion H12.
        rewrite H14 in H8.
        rewrite H13 in H8.
        rewrite H3 in H8.
        rewrite H15 in H10.
        rewrite H16 in H10.
        apply singleton_eq_iff.
        rewrite H8 H10.
        reflexivity.
     -move => y' H2.
      apply Extension in H2.
      inversion H2.
      rewrite -singleton_eq_iff.
      apply (H4 y).
      split.
      --exists x.
        split.
        apply singleton_eq_iff.
        reflexivity.
      --apply H.
  Qed.

End FunctionDefinition.
