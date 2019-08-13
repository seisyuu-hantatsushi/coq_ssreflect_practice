From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import function_composite_theories.

Section FunctionInvertible.
  Variable U:Type.
  Variables X Y: Ensemble U.
  Variables F G: U -> U.

  Definition Invertible (f: Ensemble (Ensemble (Ensemble U))) (X Y:Ensemble U) :=
    forall (idX idY: Ensemble (Ensemble (Ensemble U))),
      IdentityMapping idX X /\ IdentityMapping idY Y ->
      exists g:Ensemble (Ensemble (Ensemble U)), g ∘ f = idX /\ f ∘ g = idY.

  Lemma exists_traspose_mapping:
    forall (f: Ensemble (Ensemble (Ensemble U))) (y:U),
      (exists x:U, (|x,y|) ∈ f) <-> (exists x:U, (|y,x|) ∈ f^-1).
  Proof.
    move => f y.
    rewrite /iff.
    split => H; inversion H; exists x.
    +split.
     apply H0.
    +inversion H0.
     apply ordered_pair_swap in H1.
     rewrite H1 in H2.
     apply H2.
  Qed.

  Theorem double_inverse_mapping:
    forall (f: Ensemble (Ensemble (Ensemble U))),
      f ≔ F ⊢ X ⟼ Y /\ Bijection f Y -> (f ^-1)^-1 = f.
  Proof.
    move => f.
    case => [[Hf HfS] [HBI HBS]].
    apply /Extensionality_Ensembles.
    split => Z H.
    +inversion H.
     inversion H0.
     apply ordered_pair_swap in H2.
     rewrite H2 in H3.
     apply H3.
    +rewrite Hf in H.
     inversion H.
     split.
     split.
     rewrite Hf.
     split.
     apply H0.
  Qed.

  Theorem unfold_inverse_composite_of_mapping:
    forall (f g: Ensemble (Ensemble (Ensemble U))) (W:Ensemble U),
      f ≔ F ⊢ X ⟼ Y /\ Bijection f Y /\ g ≔ G ⊢ Y ⟼ W /\ Bijection g W ->
      (g ∘ f)^-1 = f^-1 ∘ g^-1.
  Proof.
    move => f g W.
    case => [[Hf HfS] [[HBIf HBSf] [[Hg HgS] [HBIg HBSg]]]].
    apply /Extensionality_Ensembles.
    split => Z H; inversion H.
    inversion H0.
    inversion H3 as [z].
    +split.
     exists z.
     apply ordered_pair_iff in H2.
     inversion H2.
     rewrite H5 in H4.
     rewrite H6 in H4.
     inversion H4.
     split; split.
     apply H8.
     apply H7.
    +split.
     split.
     inversion H0 as [z].
     inversion H2.
     inversion H3.
     apply ordered_pair_swap in H5.
     rewrite H5 in H6.
     inversion H4.
     apply ordered_pair_swap in H7.
     rewrite H7 in H8.
     exists z.
     split.
     apply H8.
     apply H6.
  Qed.

  Theorem inverse_mapping_is_mapping:
    forall (f: Ensemble (Ensemble (Ensemble U))),
      f ≔ F ⊢ X ⟼ Y /\ Bijection f Y ->
      (forall (y x x':U), (|y,x|) ∈ f ^-1 /\ (|y,x'|) ∈ f^-1 -> x = x') /\ (forall (y:U), y ∈ Y -> exists x:U, (|y, x|) ∈ f ^-1).
  Proof.
    move => f.
    case => [[Hf HfS] [HBI HBS]].
    split.
    +move => y x x'.
     case => H H'.
     inversion H.
     apply ordered_pair_swap in H0.
     rewrite H0 in H1.
     inversion H'.
     apply ordered_pair_swap in H2.
     rewrite H2 in H3.
     apply (HBI x x' y).
     split.
     apply H1.
     apply H3.
    +move => y H.
     apply exists_traspose_mapping.
     apply HBS.
     apply H.
  Qed.

  Theorem inverse_mapping_is_bijection:
    forall (f: Ensemble (Ensemble (Ensemble U))),
      f ≔ F ⊢ X ⟼ Y /\ Bijection f Y -> Bijection (f ^-1) X.
  Proof.
    move => f.
    case => [[Hf HfS] [HBI HBS]].
    split.
    +move => y y' x.
     case => H0 H1.
     inversion H0.
     inversion H1.
     rewrite Hf in H2.
     rewrite Hf in H4.
     inversion H2 as [x2 y2 [H5]].
     inversion H4 as [x3 y3 [H8]].
     apply ordered_pair_iff in H.
     inversion H.
     apply ordered_pair_iff in H3.
     inversion H3.
     apply ordered_pair_iff in H7.
     inversion H7.
     apply ordered_pair_iff in H10.
     inversion H10.
     rewrite -H12 in H14.
     rewrite -H17 in H14.
     rewrite -H15 in H14.
     rewrite H14 in H8.
     rewrite -H5 in H8.
     rewrite H18 in H8.
     rewrite H13 in H8.
     rewrite H16 in H8.
     rewrite H11 in H8.
     apply eq_sym.
     apply H8.
    +move => x H.
     suff: exists y:U, ((|x,y|)) ∈ f.
     ++move => H00.
       inversion H00 as [y'].
       exists y'.
       split.
       apply H0.
    +apply HfS.
     apply H.
  Qed.

  Goal forall (f idX:Ensemble (Ensemble (Ensemble U))),
      f ≔ F ⊢ X ⟼ Y /\ Bijection f Y /\ IdentityMapping idX X -> f ^-1 ∘ f = idX.
  Proof.
    move => f idX.
    case => H [[HBI HBS] HidX].
    apply /Extensionality_Ensembles.
    inversion H as [Hf HfS].
    inversion HidX as [HidX0 HidX0S].
    split => Z.
    +case => x y [z].
     case => Hf0 Hfi.
     inversion Hfi as [z' y'].
     apply ordered_pair_swap in H1.
     rewrite H1 in H0.
     rewrite HidX0.
     split.
     split.
     apply (HBI y x z).
     split.
     apply H0.
     apply Hf0.
     rewrite Hf in Hf0.
     rewrite Hf in H0.
     inversion Hf0.
     rewrite H2 in H3.
     inversion H3.
     apply ordered_pair_in_direct_product_iff_and in H5.
     inversion H5.
     inversion H0.
     rewrite H8 in H9.
     inversion H9.
     apply ordered_pair_in_direct_product_iff_and in H11.
     inversion H11.
     apply ordered_pair_in_direct_product_iff_and.
     split.
     apply H6.
     apply H12.
    +move => H0.
     rewrite HidX0 in H0.
     inversion H0.
     inversion H1.
     split.
    +have L1: exists z:U, (|x,z|) ∈ f.
     ++apply HfS.
       apply ordered_pair_in_direct_product_iff_and in H4.
       inversion H4.
       apply H5.
    +inversion L1 as [z].
     exists z.
     split.
     apply H5.
     split.
     rewrite H3.
     apply H5.
  Qed.

  Goal forall (f idY:Ensemble (Ensemble (Ensemble U))),
      f ≔ F ⊢ X ⟼ Y /\ Bijection f Y /\ IdentityMapping idY Y -> f ∘ f^-1 = idY.
  Proof.
    move => f idY.
    case => H [[HBI HBS] HidY].
    apply /Extensionality_Ensembles.
    inversion H as [Hf HfS].
    inversion HidY as [HidY0 HidY0S].
    rewrite HidY0.
    split => Z.
    +case => x y [z].
     case => Hfi Hf0.
     inversion Hfi as [z' x'].
     apply ordered_pair_swap in H1.
     rewrite H1 in H0.
     rewrite Hf in Hf0.
     rewrite Hf in H0.
     inversion Hf0.
     inversion H3.
     inversion H0.
     inversion H7.
     apply ordered_pair_iff in H2.
     inversion H2.
     apply ordered_pair_iff in H6.
     inversion H6.
     rewrite H10 in H4.
     rewrite H11 in H4.
     rewrite H12 in H8.
     rewrite H13 in H8.
     rewrite -H8 in H4.
     split.
     split.
     apply H4.
     rewrite -H4.
     apply ordered_pair_in_direct_product_iff_and.
     apply ordered_pair_in_direct_product_iff_and in H5.
     inversion H5.
     rewrite H11 in H15.
     split.
     apply H15.
     apply H15.
    +move => H0.
     inversion H0.
     inversion H1.
     apply ordered_pair_in_direct_product_iff_and in H4.
     inversion H4.
    -have L1: exists z:U, (|z, y|) ∈ f.
     ++apply (HBS y).
       apply H6.
    -inversion L1 as [z].
     split.
     exists z.
     split.
     split.
     rewrite -H3.
     apply H7.
     apply H7.
  Qed.

End FunctionInvertible.
