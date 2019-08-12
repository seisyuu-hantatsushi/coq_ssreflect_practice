From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import function_composite_theories.

Section FunctionInvertible.
  Variable U:Type.
  Variables X Y: Ensemble U.
  Variables F: U -> U.

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
    unfold Injection in HBI.
    unfold Surjection in HBS.
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
    +unfold Surjection.
     move => x H.
     suff: exists y:U, ((|x,y|)) ∈ f.
     ++move => H00.
       inversion H00 as [y'].
       exists y'.
       split.
       apply H0.
    +apply HfS.
     apply H.
  Qed.

  Goal 
  
End FunctionInvertible.