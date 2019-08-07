From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import function_theories.

Section FunctionCompositeTheories.
  Variable U:Type.
  Variables F G H: U -> U.
  Variables A B C D: Ensemble U.

  Theorem function_composite_assoc:
    forall (f g h: Ensemble (Ensemble (Ensemble U))),
      f ≔ F ⊢ A ⟼ B /\ g ≔ F ⊢ B ⟼ C /\ h ≔ H ⊢ C ⟼ D -> h ∘ (g ∘ f) = (h ∘ g) ∘ f.
  Proof.
    move => f g h.
    case => [[Hf HfS] [[Hg HgS] [Hh HhS]]].
    apply /Extensionality_Ensembles.
    split => Z H0.
    +inversion H0.
     inversion H1 as [z].
     inversion H3.
     inversion H4.
     inversion H7 as [z'].
     inversion H8.
     split.
     exists z'.
     split.
     apply ordered_pair_iff in H6.
     inversion H6.
     rewrite -H11.
     apply H9.
     split.
     exists z.
     split.
     apply ordered_pair_iff in H6.
     inversion H6.
     rewrite -H12.
     apply H10.
     apply H5.
    +inversion H0.
     inversion H1 as [z].
     inversion H3.
     inversion H5.
     inversion H7 as [z'].
     inversion H8.
     apply ordered_pair_iff in H6.
     inversion H6.
     split.
     exists z'.
     split.
     split.
     exists z.
     split.
     ++apply H4.
       rewrite -H11.
       apply H9.
     ++rewrite -H12.
       apply H10.
  Qed.

  Theorem function_composite_image:
    forall (f g: Ensemble (Ensemble (Ensemble U))) (x:U),
      x ∈ A /\ f ≔ F ⊢ A ⟼ B /\ g ≔ F ⊢ B ⟼ C ->
      (g ∘ f) '' {| x |} = g '' (f '' {| x |}).
  Proof.
    move => f g x.
    case => HA [[Hf HfS] [Hg HgS]].
    apply /Extensionality_Ensembles.
    split => y H0.
    +inversion H0 as [y'].
     inversion H1 as [x'].
     inversion H3.
     inversion H5.
     inversion H7 as [z].
     inversion H8.
     apply ordered_pair_iff in H6.
     inversion H6.
     apply singleton_eq_iff in H4.
     split.
     exists z.
     split.
     split.
     exists x.
     split.
     apply singleton_eq_iff.
     reflexivity.
     rewrite -H4.
     rewrite -H11.
     apply H9.
     rewrite -H12.
     apply H10.
    +inversion H0.
     inversion H1 as [z].
     inversion H3.
     split.
     exists x.
     split.
     apply singleton_eq_iff.
     reflexivity.
     split.
     exists z.
     inversion H4.
     inversion H6 as [x'].
     inversion H8.
     apply singleton_eq_iff in H9.
     rewrite H9 in H10.
     split.
     apply H10.
     apply H5.
  Qed.

  Goal forall (f idA: Ensemble (Ensemble (Ensemble U))),
      f ≔ F ⊢ A ⟼ B /\ IdentityMapping idA A -> f = f ∘ idA.
  Proof.
    move => f idA.
    case => [[Hf HfS] [HidA HidAS]].
    apply /Extensionality_Ensembles.
    rewrite Hf HidA.
    split => Z H0.
    +inversion H0 as [x y].
     inversion H1.
     split.
     exists x.
     split.
     split.
     split.
     reflexivity.
     inversion H4.
     inversion H5 as [x' [y']].
     inversion H7.
     inversion H9.
     apply ordered_pair_iff in H11.
     inversion H11.
     rewrite H12.
     split.
     exists x'.
     exists x'.
     split.
     apply H8.
     split.
     apply H8.
     done.
     rewrite H2.
     apply H0.
    +inversion H0.
     inversion H1.
     inversion H3.
     inversion H4.
     inversion H7.
     apply ordered_pair_iff in H6.
     inversion H6.
     rewrite -H10.
     rewrite -H8.
     rewrite H11.
     apply H5.
  Qed.

End FunctionCompositeTheories.
