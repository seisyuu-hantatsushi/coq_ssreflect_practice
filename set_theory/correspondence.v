From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import logic_pred_theories.
Require Import class_set.
Require Import direct_product_theories.
Require Import binary_relation.

Inductive GraphOfBinaryRelation {U:Type} (R:BinaryRelation U) (A B: Ensemble U): Ensemble (Ensemble (Ensemble U)) :=
| Definition_of_Graph: forall (x y:U), R x y /\ (|x, y|) ∈ A × B -> (|x, y|) ∈ GraphOfBinaryRelation R A B.

Inductive DomainOfCorrespondence {U:Type} (f:Ensemble (Ensemble (Ensemble U))) : Ensemble U :=
| Definition_of_DomainOfCorrespondence: forall (x:U), x ∈ Pr1 f -> x ∈ DomainOfCorrespondence f.

Inductive RangeOfCorrespondence {U:Type} (f:Ensemble (Ensemble (Ensemble U))) : Ensemble U :=
| Definition_of_RangeOfCorrespondence: forall (y:U), y ∈ Pr2 f -> y ∈ RangeOfCorrespondence f.

Inductive ImageOfCorrespondence {U:Type} (f:Ensemble (Ensemble (Ensemble U))) (C:Ensemble U) : Ensemble U :=
  | Definition_of_ImageOfCorrespondence: forall (y:U), (exists x:U, x ∈ C /\ (|x,y|) ∈ f) -> y ∈ ImageOfCorrespondence f C.

Inductive CompoundCorrespondence {U:Type} (g f:Ensemble (Ensemble (Ensemble U))) : Ensemble (Ensemble (Ensemble U)) :=
| Definition_of_CompoundCorrespondence :
    forall (x y:U), (exists z:U, (|x,z|) ∈ f /\ (|z,y|) ∈ g) -> (|x,y|) ∈ CompoundCorrespondence g f.

Inductive TransposeOfGraph {U:Type} (f:Ensemble (Ensemble (Ensemble U))) :
    Ensemble (Ensemble (Ensemble U)) :=
| Definition_of_InverseCorrespondence :
    forall (x y: U), (|x,y|) ∈ f -> (|y,x|) ∈ TransposeOfGraph f.

(* ⥴: Unicode 2974 (RIGHTWARDS ARROW ABOVE TILDE OPERATO) *)
(* ≔ : Unicode 2254 (COLON EQUAL) *)
(* ⊦ : Unicode 22A6 (ASSERTION) *)
Notation "f ≔ R ⊦ A ⥴ B" := (f = GraphOfBinaryRelation R A B) (at level 44).

(* ∘: Unicode 2218 *)
Notation "g ∘ f" := (CompoundCorrespondence g f) (at level 45).

(* 𝕯: Unicode:1D56F, 𝕽: Unicode:1D57D *)
Notation "𝕯( f )" := (DomainOfCorrespondence f) (at level 45).
Notation "𝕽( f )" := (RangeOfCorrespondence f) (at level 45).

Notation "f ^-1" := (TransposeOfGraph f) (at level 44).

Notation "f '' A" := (ImageOfCorrespondence f A) (at level 46).

Proposition transpose_correspondence_iff:
  forall (U:Type) (x y:U) (R:BinaryRelation U) (A B:Ensemble U) (f:Ensemble (Ensemble (Ensemble U))),
      f ≔ R ⊦ A ⥴ B -> (|x,y|) ∈ f <-> (|y,x|) ∈ f^-1.
  Proof.
    move => U x y R A B f H.
    rewrite /iff.
    split => H0.
    split.
    apply H0.
    inversion H0.
    apply ordered_pair_swap in H1.
    rewrite H1 in H2.
    apply H2.
  Qed.

Section Correspondence.
  Variable U: Type.
  Variable R: BinaryRelation U.
  Variable A B C D: Ensemble U.

  Proposition graph_is_included_in_direct_product:
    forall (f:Ensemble (Ensemble (Ensemble U))),
      f ≔ R ⊦ A ⥴ B -> f ⊂ A × B.
  Proof.
    move => f H.
    rewrite H => X.
    case => [x y [H0]].
    apply.
  Qed.

  Proposition domain_of_graph_is_included_in_source_set:
    forall (f:Ensemble (Ensemble (Ensemble U))),
      f ≔ R ⊦ A ⥴ B -> 𝕯( f ) ⊂ A.
  Proof.
    move => f H x H0.
    inversion H0 as [x' H1].
    inversion H1 as [x0 [y0]].
    rewrite H in H3.
    rewrite -H4 in H3.
    inversion H3.
    inversion H6.
    rewrite H5 in H8.
    apply ordered_pair_in_direct_product_iff_and in H8.
    inversion H8.
    rewrite -H4.
    apply H9.
  Qed.

  Proposition range_of_graph_is_included_in_source_set:
    forall (f:Ensemble (Ensemble (Ensemble U))),
      f ≔ R ⊦ A ⥴ B -> 𝕽( f ) ⊂ B.
  Proof.
    move => f H y H0.
    inversion H0 as [y' [y0 [x]]].
    rewrite H in H1.
    inversion H1 as [x1 y1 [HR H3]].
    rewrite H4 in H3.
    apply ordered_pair_in_direct_product_iff_and in H3.
    inversion H3.
    apply H6.
  Qed.

  Proposition singleton_image_to_direct_product:
    forall (f:Ensemble (Ensemble (Ensemble U))),
      f ≔ R ⊦ A ⥴ B -> forall (x y:U), {|y|} = f '' {|x|} -> (|x,y|) ∈ f.
  Proof.
    move => f Hf x y H.
    rewrite Hf in  H.
    apply Extension in H.
    inversion H.
    rewrite Hf.
    move: (H0 y).
    case.
    apply singleton_eq_iff.
    reflexivity.
    move => y0 H2.
    inversion H2 as [x0 []].
    apply singleton_eq_iff in H3.
    rewrite -H3.
    apply H4.
  Qed.

  Theorem union_of_image_of_correspondence_eq:
    forall (f:Ensemble (Ensemble (Ensemble U))),
      f ≔ R ⊦ A ⥴ B -> f '' (C ∪ D) = f '' C ∪ f '' D.
  Proof.
    move => f H.
    apply Extensionality_Ensembles.
    split => z.
    +case => [y [x [H0 H1]]].
     inversion H0 as [x' H2|x' H2]; [left|right]; split; exists x; split.
     ++apply H2.
       apply H1.
     ++apply H2.
       apply H1.
    +case => z0; case => [y [x [H' H0]]]; split; exists x; split.
     ++left.
       apply H'.
       apply H0.
     ++right.
       apply H'.
       apply H0.
  Qed.

  Theorem and_image_of_correspondence_included:
    forall (f:Ensemble (Ensemble (Ensemble U))),
      f ≔ R ⊦ A ⥴ B -> f '' (C ∩ D) ⊂ (f '' C ∩ f '' D).
  Proof.
    move => f H y H0.
    inversion H0 as [y' [x' [H1 H2]]].
    inversion H1.
    split; split; exists x; rewrite H6; split.
    apply H4.
    apply H2.
    apply H5.
    apply H2.
  Qed.

  Theorem included_domain_to_included_image:
    forall (f:Ensemble (Ensemble (Ensemble U))) (V W:Ensemble U),
      f ≔ R ⊦ A ⥴ B -> V ⊂ W /\ W ⊂ A -> (f '' V ⊂ f '' W).
  Proof.
    move => f V W HF.
    case => [HVW HWA] y H0.
    inversion H0 as [y0 [x [H1 H2]]].
    split.
    exists x.
    split.
    apply HVW.
    apply H1.
    apply H2.
  Qed.

  Proposition doube_transpose:
    forall (f:Ensemble (Ensemble (Ensemble U))),
      f ≔ R ⊦ A ⥴ B -> (f^-1)^-1 = f.
  Proof.
    move => f H.
    apply /Extensionality_Ensembles.
    split => Z H0.
    +inversion H0.
     rewrite transpose_correspondence_iff.
     apply H1.
     apply H.
    +rewrite H in H0.
     inversion H0.
     rewrite -H2 in H0.
     rewrite -H in H0.
     split; split.
     apply H0.
  Qed.

  Goal forall (f:Ensemble (Ensemble (Ensemble U))),
      f ≔ R ⊦ A ⥴ B -> f '' (C ∩ D) ⊂ f '' C ∩ f '' D.
  Proof.
    move => f H x H0.
    inversion H0 as [x0 [y' [H1 H2]]].
    inversion H1.
    split; split; exists y'; split.
    +apply H4.
     apply H2.
    +apply H5.
     apply H2.
  Qed.

  (* g ∘ f (D) = g(f(D)) *)
  Proposition image_compound_correspondence_eq:
    forall (F G:BinaryRelation U) (f g:Ensemble (Ensemble (Ensemble U))),
      f ≔ F ⊦ A ⥴ B /\ g ≔ G ⊦ B ⥴ C -> g ∘ f '' D = g '' (f '' D).
  Proof.
    move => F G f g.
    case => HF HG.
    apply Extensionality_Ensembles.
    split => y H.
    +inversion H as [y0 [x0 []]].
     inversion H1 as [x1 y1 [z [H3 H4]]].
     apply ordered_pair_iff in H5.
     inversion H5.
     split.
     exists z.
     split.
     ++split.
       exists x1.
       split.
       rewrite H6.
       apply H0.
       apply H3.
     ++rewrite -H7.
       apply H4.
    +inversion H as [y0 [z []]].
     inversion H0 as [y0' [x []]].
     split.
     exists x.
     split.
     apply H3.
     split.
     exists z.
     split.
     apply H4.
     apply H1.
  Qed.

  (* h ∘ (g ∘ f) = (h ∘ g) ∘ f *)
  Theorem compound_correspondence_assoc:
    forall (X Y Z W:Ensemble U) (F G H:BinaryRelation U) (f g h:Ensemble (Ensemble (Ensemble U))),
      f ≔ F ⊦ X ⥴ Y /\ g ≔ G ⊦ Y ⥴ Z /\ h ≔ H ⊦ Z ⥴ W ->
      h ∘ (g ∘ f) = (h ∘ g) ∘ f.
  Proof.
    move => X Y Z W F G H f g h.
    case => HF [HG HH].
    apply Extensionality_Ensembles.
    split => V H0.
    +inversion H0 as [x y [z0 []]].
     inversion H1 as [x0 z0' [z1 []]].
     apply ordered_pair_iff in H6.
     inversion H6.
     split.
     exists z1.
     split.
     rewrite -H7.
     apply H4.
     split.
     exists z0'.
     split.
     apply H5.
     rewrite H8.
     apply H2.
    +inversion H0 as [x y [z0 []]].
     inversion H2 as [z0' y0 [z1 []]].
     apply ordered_pair_iff in H6.
     inversion H6.
     split.
     exists z1.
     split.
     split.
     exists z0.
     split.
     apply H1.
     rewrite -H7.
     apply H4.
     rewrite -H8.
     apply H5.
  Qed.

  (* (g ∘ f)^(-1) = f^(-1) ∘ g^(-1) *)
  Theorem unfold_compound_corrsepondence_inverse:
    forall (F G:BinaryRelation U) (f g:Ensemble (Ensemble (Ensemble U))),
      f ≔ F ⊦ A ⥴ B /\ g ≔ G ⊦ B ⥴ C -> (g ∘ f) ^-1 = f ^-1 ∘ g ^-1.
  Proof.
    move => F G f g.
    case => HF HG.
    apply Extensionality_Ensembles.
    split => X H.
    -inversion H as [x y].
     inversion H0 as [x0 y0].
     inversion H2 as [z []].
     apply ordered_pair_iff in H3.
     inversion H3.
     split.
     exists z.
     split; split.
      +rewrite H7 in H5.
       apply H5.
      +rewrite H6 in H4.
       apply H4.
    -inversion H as [x y].
     inversion H0 as [z []].
     split.
     split.
     exists z.
     split.
     apply (transpose_correspondence_iff y z HF) in H3.
     apply H3.
     apply (transpose_correspondence_iff z x HG) in H2.
     apply H2.
  Qed.

  Theorem transpose_graph_keep_included:
    forall (f:Ensemble (Ensemble (Ensemble U))),
      f ≔ R ⊦ A ⥴ B -> f ⊂ A × B <-> f^-1 ⊂ B × A.
  Proof.
    move => f HF.
    rewrite HF.
    rewrite /iff.
    split => H Z H0; inversion H0 as [x y H1].
    +inversion H1 as [x0 y0].
     inversion H3.
     rewrite H4 in H6.
     apply ordered_pair_in_direct_product_iff_and in H6.
     inversion H6.
     apply ordered_pair_in_direct_product_iff_and.
     split.
     apply H8.
     apply H7.
    +inversion H1.
     apply H4.
  Qed.

End Correspondence.

Require Export class_set.
Require Export direct_product_theories.
Require Export binary_relation.