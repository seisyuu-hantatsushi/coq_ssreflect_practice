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
      f '' (X ∪ Y) = (f '' X) ∪ (f '' Y).
  Proof.
    move => f X Y.
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

  Theorem FunctionTheory_1:
    forall (f:Ensemble (Ensemble (Ensemble U))), f = F : A ⟼ B /\ Mapping f A /\ Injection f -> forall (y x0 x1:U), (|y, x0|) ∈ f^-1 /\ (|y, x1|) ∈ f^-1 -> x0 = x1.
  Proof.
    move => f.
    case => H [HfM HIf].
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
      f = F : A ⟼ B /\ Mapping f A /\ Bijection f B -> 𝕯( f^-1 ) = B /\ 𝕽( f^-1 ) = A /\ Bijection (f^-1) A.
  Proof.
    move => f.
    case => H [ HMfA HBfB ].
    inversion HBfB as [HBfBI HBfBS].
    unfold Mapping in HMfA.
    unfold Injection in HBfBI.
    unfold Sujection in HBfBS.
    +split.
     apply /Extensionality_Ensembles.
     ++split => y.
       move => HyDfi.
       inversion HyDfi as [y'].
       inversion H0 as [y''].
       inversion H2 as [x].
       inversion H4.
       rewrite H in H6.
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
          apply H1.
          apply HBfBS.
     --apply HB.
    +split.
     apply /Extensionality_Ensembles.
     split => x.
    +move => HyRfi.
     inversion HyRfi as [x'].
     inversion H0 as [y0].
     inversion H2 as [y0'].
     inversion H4 as [x1 y1].
     apply ordered_pair_swap in H6.
     rewrite H6 in H5.
     rewrite H in H5.
     inversion H5.
     inversion H8.
     rewrite H7 in H10.
     apply ordered_pair_in_direct_product_iff_and in H10.
     inversion H10.
     apply H11.
    +move => HA.
     split.
     split.
     ++suff: exists y:U, (|x,y|) ∈ f.
       move => H0.
       inversion H0 as [y].
       exists y.
       split.
       apply H1.
    -apply HMfA.
     apply HA.
     unfold Bijection.
     split.
     unfold Injection.
     move => y y' x.
     case => H0 H1.
     inversion H0.
     inversion H1.
     apply ordered_pair_swap in H2.
     apply ordered_pair_swap in H4.
     rewrite H in H3.
     rewrite H in H5.
     inversion H3.
     inversion H7.
     inversion H5.
     inversion H11.
     rewrite H2 in H6.
     apply ordered_pair_iff in H2.
     inversion H2.
     apply ordered_pair_iff in H4.
     inversion H4.
     apply ordered_pair_iff in H6.
     inversion H6.
     apply ordered_pair_iff in H10.
     inversion H10.
     rewrite -H19.
     rewrite H8.
     rewrite H18.
     rewrite -H17.
     rewrite -H21.
     rewrite H12.
     rewrite H20.
     rewrite H16.
     reflexivity.
    +unfold Sujection.
     move => x HA.
     ++suff: exists y:U, (|x,y|) ∈ f.
       move => H0.
       inversion H0 as [y].
       exists y.
       split.
       apply H1.
    -apply HMfA.
     apply HA.
  Qed.
  
End FunctionTheories.
