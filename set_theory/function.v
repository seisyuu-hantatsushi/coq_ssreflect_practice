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

Definition Injection {U:Type} (f:Ensemble (Ensemble (Ensemble U))) :=
  forall (x x' y :U), (|x,y|) ∈ f /\ (|x',y|) ∈ f -> x = x'.

Definition Surjection {U:Type} (f:Ensemble (Ensemble (Ensemble U))) (R:Ensemble U) :=
  forall (y:U), y ∈ R -> exists x:U, (|x,y|) ∈ f.

Definition Bijection {U:Type} (f:Ensemble (Ensemble (Ensemble U))) (R:Ensemble U) :=
  Injection f /\ Surjection f R.

Definition IdentityMapping {U:Type} (f: Ensemble (Ensemble (Ensemble U))) (A: Ensemble U) :=
  MappingWithFunction f (fun x => x) A A.

(* ≔ : Unicode 2254 (COLON EQUAL) *)
(* ⊦ : Unicode 22A6 (ASSERTION) *)
(* ⟼: Unicode:27FC (LONG RIGHTWARDS ARROW FROM BAR) *)

Notation "f ≔ F ⊦ A ⟼ B" := (MappingWithFunction f F A B) (at level 43).

Section FunctionDefinition.

  Variable U:Type.
  Variable F: FunctionOfMap U.
  Variable X Y:Ensemble U.

  (*confirming that MappingWithFunction is satisified with Mapping *)
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

  (*confirming that left-total and uniqueness *)
  Goal forall (f:Ensemble (Ensemble (Ensemble U))),
      (f ≔ F ⊦ X ⟼ Y) -> forall (x:U), x ∈ 𝕯( f ) -> exists! y, {|y|} = f '' {|x|}.
  Proof.
    move => f [Hf HfS] x HxDf.
    inversion HxDf.
    inversion H.
    inversion H1 as [y].
    exists y.
    split.
    apply /Extensionality_Ensembles.
    split => y' H4.
    +apply singleton_eq_iff in H4.
     rewrite H4.
     split.
     exists x.
     split.
     done.
     apply H3.
    +inversion H4 as [y2 [x2 []]].
     rewrite Hf in H6.
     inversion H6 as [x3 y3 []].
     rewrite Hf in H3.
     inversion H3 as [x3' y3' []].
     apply singleton_eq_iff in H5.
     apply ordered_pair_iff in H10.
     inversion H10.
     apply ordered_pair_iff in H13.
     inversion H13.
     rewrite H14 in H8.
     rewrite H5 in H8.
     rewrite H15 in H8.
     rewrite H17 in H11.
     rewrite H16 in H11.
     rewrite H8 H11.
     done.
     -move => y' H4.
      apply Extension in H4.
      inversion H4.
      rewrite -singleton_eq_iff.
      apply (H6 y).
      split.
      --exists x.
        split.
        done.
      --done.
  Qed.

  (* confirming left-total *)
  Goal forall (f:Ensemble (Ensemble (Ensemble U))),
      (f ≔ F ⊦ X ⟼ Y) -> 𝕯( f ) = X.
  Proof.
    move => f [Hf HfS].
    apply /Extensionality_Ensembles.
    -split => x H.
     inversion H as [x0 [x0' [y0']]].
     rewrite Hf in H0.
     inversion H0 as [x1 y1 []].
     rewrite H4 in H3.
     apply ordered_pair_in_direct_product_iff_and in H3.
     inversion H3.
     done.
    -split.
     split.
     move: H.
     apply (HfS x).
  Qed.

End FunctionDefinition.

Require Export class_set.
Require Export direct_product_theories.
Require Export correspondence.