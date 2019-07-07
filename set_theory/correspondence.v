From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import logic_pred_theories.
Require Import class_set.
Require Import direct_product_theories.
Require Import binary_relation.

Section Correspondence.
  Variable U: Type.

  Goal forall (A B:Ensemble U) (R:BinaryRelation U), GraphOfBinaryRelation A B R ⊂ A × B.
  Proof.
    move => A B R X.
    case => [x y [H]].
    apply.
  Qed.

  Inductive Domain (f:Ensemble (Ensemble (Ensemble U))) : Ensemble U :=
  | Definition_of_Domain: forall (x:U), x ∈ Pr1 f -> x ∈ Domain f.

  Inductive Range (f:Ensemble (Ensemble (Ensemble U))) : Ensemble U :=
  | Definition_of_Range: forall (y:U), y ∈ Pr2 f -> y ∈ Range f.

  Goal forall (A B:Ensemble U) (R:BinaryRelation U), Domain (GraphOfBinaryRelation A B R) ⊂ A.
  Proof.
    move => A B R X.
    case => [Z [x [y H]]].
    inversion H.
    inversion H1.
    rewrite H0 in H3.
    apply ordered_pair_in_direct_product_iff_and in H3.
    inversion H3.
    apply H4.
  Qed.

  Goal forall (A B:Ensemble U) (R:BinaryRelation U), Range (GraphOfBinaryRelation A B R) ⊂ B.
  Proof.
    move => A B R X.
    case => [Z [y [x H]]].
    inversion H.
    inversion H1.
    rewrite H0 in H3.
    apply ordered_pair_in_direct_product_iff_and in H3.
    inversion H3.
    apply H5.
  Qed.

  Inductive Image (f:Ensemble (Ensemble (Ensemble U))) (C:Ensemble U) : Ensemble U :=
  | Definition_of_Image: forall (y:U), (exists x:U, x ∈ C /\ (|x,y|) ∈ f) -> y ∈ Image f C.

  Goal forall (A B C:Ensemble U) (R:BinaryRelation U),
      forall y:U, (y ∈ Image (GraphOfBinaryRelation A B R) C) <-> exists x:U, (x ∈ C /\ (|x, y|) ∈ GraphOfBinaryRelation A B R).
  Proof.
    move => A B C R y.
    rewrite /iff.
    split.
    case => y0.
    apply.
    case => [x [HxC H]].
    split.
    exists x.
    split.
    apply HxC.
    apply H.
  Qed.

  Theorem union_of_image_of_correspondence_eq:
    forall (A B C D:Ensemble U) (R:BinaryRelation U),
      Image (GraphOfBinaryRelation A B R) (C ∪ D) = Image (GraphOfBinaryRelation A B R) C ∪ Image (GraphOfBinaryRelation A B R) D.
  Proof.
    move => A B C D R.
    apply Extensionality_Ensembles.
    split => z.
    +case => [y [x [H0 H1]]].
     inversion H0.
     ++left.
       split.
       exists x.
       split.
       apply H.
       apply H1.
     ++right.
       split.
       exists x.
       split.
       apply H.
       apply H1.
    +case => z0.
     ++case => [y [x [HC H]]].
       split.
       exists x.
       split.
       left.
       apply HC.
       apply H.
     ++case => [y [x [HD H]]].
       split.
       exists x.
       split.
       right.
       apply HD.
       apply H.
  Qed.

  Theorem and_image_of_correspondence_included:
    forall (A B C D:Ensemble U) (R:BinaryRelation U),
      Image (GraphOfBinaryRelation A B R) (C ∩ D) ⊂ (Image (GraphOfBinaryRelation A B R) C ∩ Image (GraphOfBinaryRelation A B R) D).
  Proof.
    move => A B C D R z.
    case => [y [x [H H1]]].
    inversion H as [x0 HC HD].
    split.
    split.
    exists x.
    split.
    apply HC.
    apply H1.
    split.
    exists x.
    split.
    apply HD.
    apply H1.
  Qed.

  Goal forall (A B:Ensemble U) (R:BinaryRelation U),
      forall x y:U, (y ∈ Image (GraphOfBinaryRelation A B R) {|x|}) <-> (|x,y|) ∈ (GraphOfBinaryRelation A B R).
  Proof.
    move => A B R x y.
    rewrite /iff.
    split.
    case => [y0 [x0]].
    case => [H0 H1].
    apply singleton_eq_iff in H0.
    rewrite -H0.
    apply H1.
    move => H.
    split.
    exists x.
    split.
    apply singleton_eq_iff.
    reflexivity.
    apply H.
  Qed.

  Theorem included_domain_to_included_image:
    forall (A B V W:Ensemble U) (R:BinaryRelation U),
      V ⊂ W /\ W ⊂ Domain (GraphOfBinaryRelation A B R) -> (Image (GraphOfBinaryRelation A B R) V ⊂ Image (GraphOfBinaryRelation A B R) W).
  Proof.
    move => A B V W R.
    case => [HVW HYDG y].
    move => H.
    inversion H as [y0 [x]].
    inversion H0.
    split.
    exists x.
    split.
    apply HVW.
    apply H2.
    apply H3.
  Qed.

  Inductive InverseCorrespondence (f:Ensemble (Ensemble (Ensemble U))) :
    Ensemble (Ensemble (Ensemble U)) :=
  | Definition_of_InverseCorrespondence :
      forall (x y:U), (|x,y|) ∈ f -> (|y , x|) ∈ InverseCorrespondence f.

  Goal forall (x y:U) (A B:Ensemble U) (R:BinaryRelation U), (|x,y|) ∈ (GraphOfBinaryRelation A B R) <-> (|y,x|) ∈ InverseCorrespondence (GraphOfBinaryRelation A B R).
  Proof.
    move => x y A B R.
    rewrite /iff.
    split.
    move => H.
    split.
    apply H.
    move => H.
    inversion H.
    apply ordered_pair_iff in H0.
    inversion H0.
    rewrite -H2.
    rewrite -H3.
    apply H1.
  Qed.

  Goal forall (A B:Ensemble U) (R:BinaryRelation U), Domain (GraphOfBinaryRelation A B R) = Range (InverseCorrespondence (GraphOfBinaryRelation A B R)).
  Proof.
    move => A B R.
    apply Extensionality_Ensembles.
    split.
    move => x H.
    split.
    split.
    inversion H.
    inversion H0.
    inversion H2 as [y].
    exists y.
    split.
    apply H4.
    move => x H.
    inversion H as [x0].
    inversion H0 as [x1].
    inversion H2 as [y].
    inversion H4.
    split.
    split.
    exists y.
    apply ordered_pair_iff in H5.
    inversion H5.
    rewrite H7 in H6.
    rewrite H8 in H6.
    apply H6.
  Qed.

  Inductive CompoundCorrespondence (f:Ensemble (Ensemble (Ensemble U))) (g:Ensemble (Ensemble (Ensemble U))) : Ensemble (Ensemble (Ensemble U)) :=
  | Definition_of_CompoundCorrespondence :
      forall (x y:U), (exists z:U, (|x,z|) ∈ f /\ (|z,y|) ∈ g) -> (|x,y|) ∈ CompoundCorrespondence f g.

  
End Correspondence.




