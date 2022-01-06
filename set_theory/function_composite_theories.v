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
      f ≔ F ⊦ A ⟼ B /\ g ≔ G ⊦ B ⟼ C /\ h ≔ H ⊦ C ⟼ D -> h ∘ (g ∘ f) = (h ∘ g) ∘ f.
  Proof.
    move => f g h.
    case => [[Hf HfS] [[Hg HgS] [Hh HhS]]].
    move: (compound_correspondence_assoc) => H0.
    apply (H0 U A B C D (fun (x y:U) => y = F x) (fun (x y:U) => y = G x) (fun (x y:U) => y = H x) f g h).
    split.
    apply Hf.
    split.
    apply Hg.
    apply Hh.
  Qed.

  Theorem function_composite_image:
    forall (f g: Ensemble (Ensemble (Ensemble U))) (X:Ensemble U),
      X ⊂ A /\ f ≔ F ⊦ A ⟼ B /\ g ≔ G ⊦ B ⟼ C ->
      (g ∘ f) '' X = g '' (f '' X).
  Proof.
    move => f g X.
    case => HA [[Hf HfS] [Hg HgS]].
    move: image_compound_correspondence_eq => H0.
    apply (H0 U A B C X (fun x y:U => y = F x) (fun x y:U => y = G x) f g).
    split; done.
  Qed.

  Theorem function_composite_value:
    forall (f g: Ensemble (Ensemble (Ensemble U))) (x:U),
      x ∈ A /\ f ≔ F ⊦ A ⟼ B /\ g ≔ G ⊦ B ⟼ C ->
      (g ∘ f) '' {| x |} = g '' (f '' {| x |}).
  Proof.
    move => f g x.
    case => HA [Hf Hg].
    move: function_composite_image => H0.
    apply (H0 f g {|x|}).
    split.
    move => x' Hx'.
    apply singleton_eq_iff in Hx'.
    rewrite Hx'.
    done.
    split; done.
  Qed.

  Goal forall (f idA: Ensemble (Ensemble (Ensemble U))),
      f ≔ F ⊦ A ⟼ B /\ IdentityMapping idA A -> f = f ∘ idA.
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

  Goal forall (f idB: Ensemble (Ensemble (Ensemble U))),
      f ≔ F ⊦ A ⟼ B /\ IdentityMapping idB B -> f = idB ∘ f.
  Proof.
    move => f idB.
    case => [[Hf HfS] [HidB HidBS]].
    rewrite Hf HidB.
    apply /Extensionality_Ensembles.
    split => Z H0.
    +inversion H0 as [x y].
     inversion H1.
     inversion H4.
     inversion H5 as [x' [y']].
     inversion H7 as [H8 [H9 H10]].
     apply ordered_pair_iff in H10.
     inversion H10.
     split.
     exists y.
     split.
     rewrite H2.
     apply H0.
     split.
     split.
     reflexivity.
     split.
     exists y'.
     exists y'.
     split.
     apply H9.
     split.
     apply H9.
     rewrite H12.
     done.
    +inversion H0.
     inversion H1 as [z [H3 H4]].
     inversion H4 as [x' y' [H5 H6]].
     rewrite H5 in H7.
     apply ordered_pair_iff in H7.
     inversion H7.
     rewrite H8 in H9.
     rewrite -H9.
     apply H3.
  Qed.

End FunctionCompositeTheories.

Require Export function_theories.
