From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import function.

Section FunctionTheories.

  Variable U:Type.
  Variable F: U -> U.
  Variables A B: Ensemble U.

  Theorem union_function_domain:
    forall (f:Ensemble (Ensemble (Ensemble U))) (X Y:Ensemble U),
      (f ≔ F ⊢ A ⟼ B) -> f '' (X ∪ Y) = (f '' X) ∪ (f '' Y).
  Proof.
    move => f X Y Hf0.
    apply /Extensionality_Ensembles.
    +split => y H.
     inversion H.
     inversion H0 as [x0].
     inversion H2.
     inversion H3.
     left.
     split.
     exists x0.
     split.
     apply H5.
     apply H4.
     right.
     split.
     exists x0.
     split.
     apply H5.
     apply H4.
    +inversion H as [y0 | y0].
     inversion H0.
     inversion H2 as [x0].
     inversion H4.
     split.
     exists x0.
     split.
     left.
     apply H5.
     apply H6.
     inversion H0.
     inversion H2 as [x0].
     inversion H4.
     split.
     exists x0.
     split.
     right.
     apply H5.
     apply H6.
  Qed.

  Theorem union_inversion_mapping_domain:
    forall (f:Ensemble (Ensemble (Ensemble U))) (X Y:Ensemble U),
      (f ≔ F ⊢ A ⟼ B) -> f^-1 '' (X ∪ Y) = (f^-1 '' X) ∪ (f^-1 '' Y).
  Proof.
    move => f X Y H.
    inversion H as [Hf HfS].
    apply /Extensionality_Ensembles.
    +split => x H0.
     inversion H0 as [x0 [y0 H1]].
     rewrite -H2 in H1.
     inversion H1.
     inversion H3 as [y0' | y0'].
     inversion H4 as [x1 y1].
     ++left.
       split.
       exists y0.
       split.
       apply H5.
       rewrite -H2.
       rewrite -H8.
       split.
       apply H7.
     ++right.
       split.
       exists y0.
       split.
       apply H5.
       rewrite -H2.
       apply H4.
    +split.
     ++inversion H0.
       inversion H1 as [x0'].
       inversion H3 as [y].
       inversion H5.
       inversion H7 as [x1 y1].
       exists y.
       split.
       left.
       apply H6.
       apply H7.
     ++inversion H1 as [x0'].
       inversion H3 as [y].
       inversion H5.
       exists y.
       split.
       right.
       apply H6.
       apply H7.
  Qed.

  Theorem intersction_inversion_mapping_domain:
    forall (f:Ensemble (Ensemble (Ensemble U))) (X Y:Ensemble U),
      (f ≔ F ⊢ A ⟼ B) -> f^-1 '' (X ∩ Y) = (f^-1 '' X) ∩ (f^-1 '' Y).
  Proof.
    move => f X Y H.
    unfold Mapping in H.
    inversion H as [Hf HfS].
    rewrite Hf.
    apply /Extensionality_Ensembles.
    split => x H0.
    +inversion H0 as [x'].
     inversion H1 as [y].
     inversion H3.
     inversion H4 as [y'].
     split; split; exists y; split.
     apply H6.
     apply H5.
     apply H7.
     apply H5.
    +inversion H0 as [x'].
     inversion H1 as [x0].
     inversion H4 as [y].
     inversion H6.
     inversion H2 as [x0'].
     inversion H9 as [y'].
     inversion H11.
     inversion H8 as [x2 y2].
     inversion H14.
     inversion H13 as [x3 y3].
     inversion H18 as [x3' y3'].
     inversion H17.
     inversion H20.
     apply ordered_pair_iff in H15.
     inversion H15.
     apply ordered_pair_iff in H16.
     inversion H16.
     apply ordered_pair_iff in H19.
     inversion H19.
     apply ordered_pair_iff in H21.
     inversion H21.
     rewrite H28 in H22.
     rewrite H32 in H24.
     rewrite H27 in H22.
     rewrite H31 in H24.
     rewrite -H22 in H24.
     rewrite H33 in H24.
     rewrite H30 in H24.
     rewrite H29 in H24.
     rewrite H26 in H24.
     rewrite H24 in H12.
     split.
     exists y.
     split.
     split.
     apply H7.
     apply H12.
     rewrite H24 in H13.
     apply H13.
  Qed.

  Theorem FunctionTheory_1:
    forall (f:Ensemble (Ensemble (Ensemble U))),
      f ≔ F ⊢ A ⟼ B /\ Injection f -> forall (y x0 x1:U), (|y, x0|) ∈ f^-1 /\ (|y, x1|) ∈ f^-1 -> x0 = x1.
  Proof.
    move => f.
    case => [H HIf].
    move => y x0 x1.
    case => H0 H1.
    inversion H0.
    inversion H1.
    apply ordered_pair_swap in H2.
    apply ordered_pair_swap in H4.
    rewrite H2 in H3.
    rewrite H4 in H5.
    apply (HIf x0 x1 y).
    split.
    apply H3.
    apply H5.
  Qed.

  Theorem FunctionTheories_2:
    forall (f:Ensemble (Ensemble (Ensemble U))),
      f ≔ F ⊢ A ⟼ B /\ Bijection f B -> 𝕯( f^-1 ) = B /\ 𝕽( f^-1 ) = A /\ Bijection (f^-1) A.
  Proof.
    move => f.
    case => Hf0 [ HSfI HSfB ].
    inversion Hf0 as [Hf HfS].
    +split.
     apply /Extensionality_Ensembles.
     ++split => y.
       move => H.
       inversion H as [y' ].
       inversion H0 as [y''].
       inversion H2 as [x].
       inversion H4.
       rewrite Hf in H6.
       inversion H6.
       inversion H8.
       rewrite H7 in H10.
       apply ordered_pair_swap in H5.
       rewrite H5 in H10.
       apply ordered_pair_in_direct_product_iff_and in H10.
       inversion H10.
       apply H12.
     ++move => HB.
       split.
       split.
       +++suff: exists x:U, (|x,y|) ∈ f.
          move => H0.
          inversion H0.
          exists x.
          split.
          apply H.
          apply HSfB.
     --apply HB.
    +split.
     apply /Extensionality_Ensembles.
     split => x.
    +move => HyRfi.
     inversion HyRfi as [x0].
     inversion H as [y0].
     inversion H1 as [y0'].
     inversion H3 as [x1 y1].
     apply ordered_pair_swap in H5.
     rewrite H5 in H4.
     rewrite Hf in H4.
     inversion H4.
     inversion H7.
     rewrite H6 in H9.
     apply ordered_pair_in_direct_product_iff_and in H9.
     inversion H9.
     apply H10.
    +move => HA.
     split.
     split.
     ++suff: exists y:U, (|x,y|) ∈ f.
       move => H0.
       inversion H0 as [y].
       exists y.
       split.
       apply H.
    -apply HfS.
     apply HA.
     split.
     move => y y' x.
     case => H0 H1.
     inversion H0.
     inversion H1.
     apply ordered_pair_swap in H.
     apply ordered_pair_swap in H3.
     rewrite Hf in H2.
     rewrite Hf in H4.
     inversion H2.
     inversion H6.
     inversion H4.
     inversion H10.
     rewrite H in H5.
     apply ordered_pair_iff in H.
     inversion H.
     apply ordered_pair_iff in H3.
     inversion H3.
     apply ordered_pair_iff in H5.
     inversion H5.
     apply ordered_pair_iff in H9.
     inversion H9.
     rewrite -H18.
     rewrite H7.
     rewrite H17.
     rewrite -H16.
     rewrite -H20.
     rewrite H11.
     rewrite H19.
     rewrite H15.
     reflexivity.
    +move => x HA.
     ++suff: exists y:U, (|x,y|) ∈ f.
       move => H0.
       inversion H0 as [y].
       exists y.
       split.
       apply H.
    -apply HfS.
     apply HA.
  Qed.

End FunctionTheories.

Require Export function.