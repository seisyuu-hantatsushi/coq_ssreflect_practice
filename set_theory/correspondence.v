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
      forall (x y: U), (|x,y|) ∈ f -> (|y,x|) ∈ InverseCorrespondence f.

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

  Goal forall (A B C D :Ensemble U) (R:BinaryRelation U),
      Image (InverseCorrespondence (GraphOfBinaryRelation A B R)) (C ∩ D) ⊂ (Image (InverseCorrespondence (GraphOfBinaryRelation A B R)) C) ∩ (Image (InverseCorrespondence (GraphOfBinaryRelation A B R)) D).
  Proof.
    move => A B C D R x H.
    inversion H as [x0].
    inversion H0 as [y].
    inversion H2 as [HCD].
    inversion HCD as [y2 HC HD].
    split; split; exists y; split.
    apply HC.
    apply H3.
    apply HD.
    apply H3.
  Qed.

  Inductive CompoundCorrespondence (g:Ensemble (Ensemble (Ensemble U))) (f:Ensemble (Ensemble (Ensemble U))) : Ensemble (Ensemble (Ensemble U)) :=
  | Definition_of_CompoundCorrespondence :
      forall (x y:U), (exists z:U, (|x,z|) ∈ f /\ (|z,y|) ∈ g) -> (|x,y|) ∈ CompoundCorrespondence g f.

  Goal forall (A B C D:Ensemble U) (R1 R2:BinaryRelation U),
      Image (CompoundCorrespondence (GraphOfBinaryRelation B C R2) (GraphOfBinaryRelation A B R1)) D =
      Image (GraphOfBinaryRelation B C R2) (Image (GraphOfBinaryRelation A B R1) D).
  Proof.
    move => A B C D R1 R2.
    apply Extensionality_Ensembles.
    split => y H.
    +inversion H.
     inversion H0 as [x].
     inversion H2 as [HD].
     inversion H3.
     inversion H5 as [z].
     inversion H6.
     apply ordered_pair_iff in H4.
     inversion H4.
     split.
     exists z.
     split.
     split.
     exists x.
     split.
     apply HD.
     rewrite H9 in H7.
     apply H7.
     rewrite H10 in H8.
     apply H8.
    +inversion H.
     inversion H0 as [z].
     inversion H2.
     inversion H3.
     inversion H5 as [x].
     inversion H7 as [HD].
     split.
     exists x.
     split.
     apply HD.
     split.
     exists z.
     split.
     apply H8.
     apply H4.
  Qed.
  
  Goal forall (A B C D:Ensemble U) (R1 R2 R3:BinaryRelation U),
      CompoundCorrespondence (GraphOfBinaryRelation C D R3) (CompoundCorrespondence (GraphOfBinaryRelation B C R2) (GraphOfBinaryRelation A B R1)) = CompoundCorrespondence (CompoundCorrespondence (GraphOfBinaryRelation C D R3) (GraphOfBinaryRelation B C R2)) (GraphOfBinaryRelation A B R1).
  Proof.
    move => A B C D R1 R2 R3.
    apply Extensionality_Ensembles.
    split => X H.
    +inversion H.
     inversion H0 as [z].
     inversion H2.
     inversion H3.
     inversion H6 as [z0].
     inversion H7.
     split.
     exists z0.
     apply ordered_pair_iff in H5.
     inversion H5.
     split.
     rewrite H10 in H8.
     apply H8.
     split.
     exists y0.
     split.
     apply H9.
     rewrite H11.
     apply H4.
    +inversion H.
     inversion H0 as [z].
     inversion H2.
     inversion H4.
     inversion H6 as [z0].
     inversion H7.
     split.
     exists z0.
     apply ordered_pair_iff in H5.
     inversion H5.
     split.
     split.
     exists z.
     split.
     apply H3.
     rewrite -H10.
     apply H8.
     rewrite -H11.
     apply H9.
  Qed.

  Goal forall (A B C:Ensemble U) (R1 R2:BinaryRelation U),
      InverseCorrespondence (CompoundCorrespondence (GraphOfBinaryRelation C B R2) (GraphOfBinaryRelation A B R1))
      = CompoundCorrespondence (InverseCorrespondence (GraphOfBinaryRelation A B R1)) (InverseCorrespondence (GraphOfBinaryRelation C B R2)).
  Proof.
    move => A B C R1 R2.
    apply Extensionality_Ensembles.
    split => X H.
    inversion H.
    inversion H0.
    inversion H3 as [z].
    inversion H4.
    apply ordered_pair_iff in H2.
    inversion H2.
    split.
    exists z.
    split.
    split.
    rewrite H8 in H6.
    apply H6.
    split.
    rewrite H7 in H5.
    apply H5.
    inversion H.
    inversion H0 as [z].
    inversion H2.
    inversion H3.
    inversion H4.
    apply ordered_pair_iff in H5.
    inversion H5.
    apply ordered_pair_iff in H7.
    inversion H7.
    split.
    split.
    exists z.
    split.
    rewrite -H12.
    rewrite -H11.
    apply H8.
    rewrite -H9.
    rewrite -H10.
    apply H6.
  Qed.

End Correspondence.








