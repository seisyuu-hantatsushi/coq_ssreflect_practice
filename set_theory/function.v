From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import class_set.
Require Import direct_product_theories.

Definition FunctionOfMap {U:Type} := U -> U.

Inductive GraphOfMap {U:Type} (A B:Ensemble U) (f:FunctionOfMap) : Ensemble (Ensemble (Ensemble U)) :=
| Definition_of_GraphOfMap: forall (x y:U), y = f x /\ (|x,y|) ∈ A × B -> (|x,y|) ∈ GraphOfMap A B f.

Definition Mapping {U:Type} (f: Ensemble (Ensemble (Ensemble U))) (A: Ensemble U) :=
  forall (x:U), x ∈ A -> exists y:U, (|x, y|) ∈ f.

Inductive DomainOfMap {U:Type} (f:Ensemble (Ensemble (Ensemble U))) : Ensemble U :=
| Definition_of_DomainOfMap: forall (x:U), x ∈ Pr1 f -> x ∈ DomainOfMap f.

Inductive RangeOfMap {U:Type} (f:Ensemble (Ensemble (Ensemble U))) : Ensemble U :=
| Definition_of_RangeOfMap: forall (y:U), y ∈ Pr2 f -> y ∈ RangeOfMap f.

Inductive ImageOfMap {U:Type} (f:Ensemble (Ensemble (Ensemble U))) (C:Ensemble U) : Ensemble U :=
| Definition_of_ImageOfMap: forall (y:U), (exists x:U, x ∈ C /\ (|x,y|) ∈ f) -> y ∈ ImageOfMap f C.

Inductive CompoundMap {U:Type} (g:Ensemble (Ensemble (Ensemble U))) (f:Ensemble (Ensemble (Ensemble U))) : Ensemble (Ensemble (Ensemble U)) :=
| Definition_of_CompoundMap:
    forall (x y:U), (exists z:U, (|x, z|) ∈ f /\ (|z,y|) ∈ g) -> (|x , y|) ∈ CompoundMap g f.

Inductive InverseMap {U:Type} (f:Ensemble (Ensemble (Ensemble U))) : Ensemble (Ensemble (Ensemble U)) :=
| Definition_of_InverseMap :
    forall (x y: U), (|x,y|) ∈ f -> (|y,x|) ∈ InverseMap f.

Definition Injection {U:Type} (f:Ensemble (Ensemble (Ensemble U))) :=
  forall (x x' y :U), (|x,y|) ∈ f /\ (|x',y|) ∈ f -> x = x'.

Definition Sujection {U:Type} (f:Ensemble (Ensemble (Ensemble U))) (R:Ensemble U) :=
  forall (y:U), y ∈ R -> exists x:U, (|x,y|) ∈ f.

Definition Bijection {U:Type} (f:Ensemble (Ensemble (Ensemble U))) (R:Ensemble U) :=
  Injection f /\ Sujection f R.

(* ⟼: Unicode:27FC (LONG RIGHTWARDS ARROW FROM BAR) *)
Notation "f : A ⟼ B" := (GraphOfMap A B f) (at level 43).

Notation "f ^-1" := (InverseMap f) (at level 44).

Notation "f '' A" := (ImageOfMap f A) (at level 45).

(* 𝕯: Unicode:1D56F, 𝕽: Unicode:1D57D *)
Notation "𝕯( f )" := (DomainOfMap f) (at level 45).
Notation "𝕽( f )" := (RangeOfMap f) (at level 45).

(* ∘: Unicode 2218 *)
Notation "g ∘ f" := (CompoundMap g f) (at level 46).

Section FunctionDefinition.

  Variable  U  : Type.
  Variables A B C D: Ensemble U.
  Variables F G: U -> U.

  Definition f := F : A ⟼ B.
  Definition g := G : B ⟼ C.

  (* Proofing uniqueness of function *)
  Goal Mapping f A -> forall (x y z:U), (|x,y|) ∈ f /\ (|x,z|) ∈ f -> y = z.
  Proof.
    move => H x y z.
    case => Hfy Hfz.
    inversion Hfy.
    inversion Hfz.
    inversion H1 as [H4 H5].
    inversion H3 as [H6 H7].
    apply ordered_pair_iff in H0.
    inversion H0.
    apply ordered_pair_iff in H2.
    inversion H2.
    rewrite -H11.
    rewrite H6.
    rewrite H10.
    rewrite -H9.
    rewrite H4.
    rewrite H8.
    reflexivity.
  Qed.

  Goal forall (x:U), x ∈ 𝕯( f ) -> exists! y, {|y|} = ImageOfMap f {|x|}.
    move => x HxDF.
    inversion HxDF.
    inversion H.
    inversion H1 as [y].
    exists y.
    unfold unique.
    split.
    apply /Extensionality_Ensembles.
    split => y'.
    +move => H5.
     apply singleton_eq_iff in H5.
     split.
     exists x.
     split.
     apply singleton_eq_iff.
     reflexivity.
     rewrite H5.
     apply H3.
    +move => H4.
     inversion H4 as [y0'].
     inversion H5 as [x'].
     inversion H7.
     inversion H9 as [x'' y''].
     inversion H10.
     inversion H3 as [x''' y'''].
     inversion H14.
     apply ordered_pair_iff in H11.
     inversion H11.
     apply ordered_pair_iff in H15.
     inversion H15.
     apply singleton_eq_iff in H8.
     rewrite -H21.
     rewrite -H19.
     rewrite H12.
     rewrite H16.
     rewrite H20.
     rewrite H18.
     rewrite H8.
     reflexivity.
     move => y' H5.
     apply Extension in H5.
     unfold Same_set in H5.
     inversion H5.
     apply singleton_eq_iff.
     apply (H6 y).
     split.
     exists x.
     split.
     apply singleton_eq_iff.
     reflexivity.
     apply H3.
  Qed.

  Goal Mapping f A -> 𝕯( f ) = A.
  Proof.
    move => H.
    apply /Extensionality_Ensembles.
    split => x.
    +move => HxDF.
     inversion HxDF.
     inversion H0.
     inversion H2 as [y].
     inversion H4 as [x' y'].
     inversion H5.
     rewrite H6 in H8.
     apply ordered_pair_in_direct_product_iff_and in H8.
     inversion H8.
     apply H9.
    +split.
    split.
    apply (H x).
    apply H0.
  Qed.

  Goal g ∘ f ⊂ A × C.
  Proof.
    move => Z H.
    inversion H.
    inversion H0 as [z].
    inversion H2.
    inversion H3 as [x' z'].
    inversion H5.
    rewrite H6 in H8.
    apply ordered_pair_in_direct_product_iff_and in H8.
    inversion H8.
    inversion H4 as [z'' y'].
    inversion H11.
    rewrite H12 in H14.
    apply ordered_pair_in_direct_product_iff_and in H14.
    inversion H14.
    apply ordered_pair_in_direct_product_iff_and.
    split.
    apply H9.
    apply H16.
  Qed.

  Goal forall (f0 g0: U -> U) (F0 G0:Ensemble (Ensemble (Ensemble U))),
      F0 = f0 : A ⟼ B /\ Mapping F0 A /\ G0 = g0 : C ⟼ D /\ Mapping G0 C /\ B ⊂ C -> 𝕯(G0 ∘ F0) = A /\ 𝕽(G0 ∘ F0) ⊂ D.
  Proof.
    move => f0 g0 F0 G0.
    case => HF [HFM [HG [HGM HBC]]].
    split.
    +apply /Extensionality_Ensembles.
     split => x.
     ++move => HxDGF.
       move : (HFM x) => HFMx.
       inversion HxDGF.
       inversion H.
       inversion H1 as [z].
       inversion H3 as [x' z'].
       apply ordered_pair_iff in H5.
       inversion H5.
       inversion H4 as [z''].
       inversion H8.
       rewrite HF in H9.
       inversion H9 as [x0' z0'].
       inversion H11.
       rewrite H12 in H14.
       rewrite H6 in H14.
       apply ordered_pair_in_direct_product_iff_and in H14.
       inversion H14.
       apply H15.
       move : (HFM x) => HFMx.
       move => HA.
       split.
       split.
       move : HFMx.
       case.
       apply HA.
       move => z HFz.
       move : (HGM z).
       case.
       rewrite HF in HFz.
       inversion HFz.
       inversion H0.
       rewrite H in H2.
       apply ordered_pair_in_direct_product_iff_and in H2.
       inversion H2.
       move: H4.
       apply HBC.
       move => y HGz.
       exists y.
       split.
       exists z.
       split.
       apply HFz.
       apply HGz.
    +move => y HyRGF.
     inversion HyRGF as [y'].
     inversion H.
     inversion H1 as [x].
     inversion H3 as [x0' y0'].
     inversion H4 as [z].
     inversion H6.
     rewrite HF in H7.
     rewrite HG in H8.
     apply ordered_pair_iff in H5.
     inversion H5.
     rewrite H10 in H8.
     inversion H8 as [z1 y1].
     inversion H11.
     rewrite H12 in H14.
     apply ordered_pair_in_direct_product_iff_and in H14.
     inversion H14.
     apply H16.
  Qed.

End FunctionDefinition.

Require Export class_set.
Require Export direct_product_theories.