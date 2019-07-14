From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import class_set.
Require Import direct_product_theories.

Definition FunctionOfMap {U:Type} := U -> U.

Inductive GraphOfMap {U:Type} (A B:Ensemble U) (f:FunctionOfMap) : Ensemble (Ensemble (Ensemble U)) :=
| Definition_of_GraphOfMap: forall (x y:U), y = f x /\ (|x,y|) ∈ A × B -> (|x,y|) ∈ GraphOfMap A B f.

Inductive DomainOfMap {U:Type} (f:Ensemble (Ensemble (Ensemble U))) : Ensemble U :=
| Definition_of_DomainOfMap: forall (x:U), x ∈ Pr1 f -> x ∈ DomainOfMap f.

Inductive RangeOfMap {U:Type} (f:Ensemble (Ensemble (Ensemble U))) : Ensemble U :=
| Definition_of_RangeOfMap: forall (y:U), y ∈ Pr2 f -> y ∈ RangeOfMap f.

Inductive ImageOfMap {U:Type} (f:Ensemble (Ensemble (Ensemble U))) (C:Ensemble U) : Ensemble U :=
| Definition_of_ImageOfMap: forall (y:U), (exists x:U, x ∈ C /\ (|x,y|) ∈ f) -> y ∈ ImageOfMap f C.

Inductive CompoundMap {U:Type} (g:Ensemble (Ensemble (Ensemble U))) (f:Ensemble (Ensemble (Ensemble U))) : Ensemble (Ensemble (Ensemble U)) :=
| Definition_of_CompoundMap:
    forall (x y:U), (exists z:U, (|x, z|) ∈ f /\ (|z,y|) ∈ g) -> (|x , y|) ∈ CompoundMap g f.

Inductive InverseMap {U:Type} (f:Ensemble (Ensemble (Ensemble U))) :
  Ensemble (Ensemble (Ensemble U)) :=
| Definition_of_InverseMap :
    forall (x y: U), (|x,y|) ∈ f -> (|y,x|) ∈ InverseMap f.

Definition Injection {U:Type} (f:Ensemble (Ensemble (Ensemble U))) :=
  forall (x x' y :U), (|x,y|) ∈ f /\ (|x',y|) ∈ f -> x = x'.

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
  Variables A B C: Ensemble U.
  Variables F G: U -> U.

  Definition f := F : A ⟼ B.
  Definition g := G : B ⟼ C.

  (* Proofing uniqueness of function *)
  Goal forall (x y z:U), (|x,y|) ∈ f /\ (|x,z|) ∈ f -> y = z.
  Proof.
    move => x y z.
    case.
    move => Hy Hz.
    inversion Hy as [x0 y0 H0 H1].
    inversion H0 as [H2 H3].
    inversion Hz as [x1 y1 H4 H5].
    inversion H4 as [H6 H7].
    apply ordered_pair_iff in H1.
    inversion H1 as [H8 H9].
    apply ordered_pair_iff in H5.
    inversion H5 as [H10 H11].
    rewrite H8  in H2.
    rewrite H10 in H6.
    rewrite -H6 in H2.
    rewrite H9 in H2.
    rewrite H11 in H2.
    apply H2.
  Qed.

  Goal forall (x:U), x ∈ 𝕯( f ) -> exists! y, {|y|} = ImageOfMap f {|x|}.
  Proof.
    move => x.
    case => [x0 [x1 [y H]]].
    exists y.
    unfold unique.
    split.
    apply /Extensionality_Ensembles.
    +split => y0.
     rewrite (singleton_eq_iff y0 y).
     move => H0.
     split.
     exists x1.
     split.
     rewrite singleton_eq_iff.
     reflexivity.
     rewrite H0.
     apply H.
    +move => H0.
     inversion H0.
     inversion H1.
     inversion H3.
     inversion H.
     inversion H7.
     inversion H5.
     inversion H11.
     apply singleton_eq_iff in H4.
     apply ordered_pair_iff in H6.
     inversion H6.
     apply ordered_pair_iff in H10.
     inversion H10.
     rewrite H14 in H8.
     rewrite H16 in H12.
     rewrite H4 in H12.
     rewrite -H8 in H12.
     rewrite H15 in H12.
     rewrite H17 in H12.
     apply singleton_eq_iff.
     apply H12.
     move => y'.
     move => H0.
     inversion H.
     apply ordered_pair_iff in H1.
     inversion H1.
     apply Extension in H0.
     unfold Same_set in H0.
     unfold Included in H0.
     inversion H0.
     move : (H6 y) => H7.
     move : (H5 y) => H8.
     apply (singleton_eq_iff y y') in H7.
     apply H7.
     split.
     exists x1.
     split.
     apply singleton_eq_iff.
     reflexivity.
     apply H.
  Qed.

  Goal g ∘ f ⊂ A × C.
  Proof.
    move => Z H.
    inversion H.
    inversion H0 as [z].
    inversion H2.
    inversion H3.
    inversion H6.
    rewrite H5 in H8.
    apply ordered_pair_in_direct_product_iff_and in H8.
    inversion H8.
    inversion H4.
    inversion H12.
    apply ordered_pair_in_direct_product_iff_and in H14.
    apply ordered_pair_iff in H11.
    inversion H11.
    inversion H14.
    rewrite H16 in H18.
    apply ordered_pair_in_direct_product_iff_and.
    split.
    apply H9.
    apply H18.
  Qed.

End FunctionDefinition.

Require Export class_set.
