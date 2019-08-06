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

End FunctionCompositeTheories.