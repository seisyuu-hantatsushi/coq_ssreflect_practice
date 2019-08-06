From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import class_set.
Require Import direct_product_theories.

Definition FunctionOfMap {U:Type} := U -> U.

Inductive GraphOfMap {U:Type} (A B:Ensemble U) (f:FunctionOfMap) : Ensemble (Ensemble (Ensemble U)) :=
| Definition_of_GraphOfMap: forall (x y:U), y = f x /\ (|x,y|) ∈ A × B -> (|x,y|) ∈ GraphOfMap A B f.

Definition Mapping {U:Type} (f: Ensemble (Ensemble (Ensemble U))) (F:FunctionOfMap) (A B: Ensemble U) :=
  f = GraphOfMap A B F /\ forall (x:U), x ∈ A -> exists y:U, (|x, y|) ∈ f.

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

Definition IdentityMapping {U:Type} (f: Ensemble (Ensemble (Ensemble U))) (A: Ensemble U) :=
  Mapping f (fun x => x) A A.

(* ≔ : Unicode 2254 (COLON EQUAL) *)
(* ⊦ : Unicode 22A6 (ASSERTION) *)
(* ⟼: Unicode:27FC (LONG RIGHTWARDS ARROW FROM BAR) *)

Notation "F ≔ f ⊢ A ⟼ B" := (Mapping F f A B) (at level 43).

Notation "f ^-1" := (InverseMap f) (at level 44).

Notation "f '' A" := (ImageOfMap f A) (at level 45).
in
(* 𝕯: Unicode:1D56F, 𝕽: Unicode:1D57D *)
Notation "𝕯( f )" := (DomainOfMap f) (at level 45).
Notation "𝕽( f )" := (RangeOfMap f) (at level 45).

(* ∘: Unicode 2218 *)
Notation "g ∘ f" := (CompoundMap g f) (at level 46).

Section FunctionDefinition.

  Variable  U  : Type.
  Variables A B C D: Ensemble U.
  Variables F G: U -> U.

  (* Proofing uniqueness of function *)
  Goal forall (f:Ensemble (Ensemble (Ensemble U))), (f ≔ F ⊢ A ⟼ B) -> forall (x y z:U), (|x,y|) ∈ f /\ (|x,z|) ∈ f -> y = z.
  Proof.
    unfold Mapping.
    move => f.
    case => HF H x y z.
    case => Hfy Hfz.
    rewrite HF in Hfy.
    rewrite HF in Hfz.
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

  Goal forall (f:Ensemble (Ensemble (Ensemble U))),
      (f ≔ F ⊢ A ⟼ B) ->
      forall (x:U),
        x ∈ 𝕯( f ) -> exists! y, {|y|} = ImageOfMap f {|x|}.
    unfold Mapping.
    move => f.
    case => Hf HfS.
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
     rewrite Hf in H3.
     rewrite Hf in H9.
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
     move => y' H4.
     apply Extension in H4.
     unfold Same_set in H4.
     inversion H4.
     apply singleton_eq_iff.
     apply (H6 y).
     split.
     exists x.
     split.
     apply singleton_eq_iff.
     reflexivity.
     apply H3.
  Qed.

  Goal forall (f:Ensemble (Ensemble (Ensemble U))),
      (f ≔ F ⊢ A ⟼ B) -> 𝕯( f ) = A.
  Proof.
    unfold Mapping.
    move => f.
    case => H HfS.
    apply /Extensionality_Ensembles.
    split => x.
    +move => HxDF.
     inversion HxDF.
     inversion H0.
     inversion H2 as [y].
     rewrite H in H4.
     inversion H4 as [x' y'].
     inversion H5.
     rewrite H6 in H8.
     apply ordered_pair_in_direct_product_iff_and in H8.
     inversion H8.
     apply H9.
    +split.
    split.
    apply (HfS x).
    apply H0.
  Qed.

  Goal forall (f g:Ensemble (Ensemble (Ensemble U))),
      (f ≔ F ⊢ A ⟼ B) /\ (g ≔ F ⊢ B ⟼ C) -> g ∘ f ⊂ A × C.
  Proof.
    unfold Mapping.
    move => f g.
    case => [[Hf HfS [Hg HgS]]].
    move => Z H.
    inversion H.
    inversion H0 as [z].
    inversion H2.
    rewrite Hf in H3.
    rewrite Hg in H4.
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

  Goal forall (f g:Ensemble (Ensemble (Ensemble U))),
      f ≔ F ⊢ A ⟼ B /\ g ≔ G ⊢ C ⟼ D /\ B ⊂ C -> 𝕯(g ∘ f) = A /\ 𝕽(g ∘ f) ⊂ D.
  Proof.
    unfold Mapping.
    move => f g.
    case => [[Hf HfS] [[Hg HgS] HBC]].
    split.
    +apply /Extensionality_Ensembles.
     split => x.
     ++move => H.
       inversion H.
       inversion H0 as [x1].
       inversion H2 as [z1].
       inversion H4 as [x' y].
       apply ordered_pair_iff in H6.
       inversion H6.
       inversion H5 as [z'].
       inversion H9.
       rewrite Hf in H10.
       rewrite Hg in H11.
       inversion H10 as [x0' z0'].
       inversion H12.
       rewrite H13 in H15.
       rewrite H7 in H15.
       apply ordered_pair_in_direct_product_iff_and in H15.
       inversion H15.
       apply H16.
       move : (HfS x) => HfSx.
       move => HA.
       split.
       split.
       move : HfSx.
       case.
       apply HA.
       move => z HFz.
       move : (HgS z).
       case.
       rewrite Hf in HFz.
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
     rewrite Hf in H7.
     rewrite Hg in H8.
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

  Goal forall (f:Ensemble (Ensemble (Ensemble U))) (x:U),
      x ∈ A /\ IdentityMapping f A -> f '' {|x|} = {|x|}. 
  Proof.
    move => f x.
    unfold IdentityMapping.
    unfold Mapping.
    case => HA [H HfS].
    rewrite H.
    apply /Extensionality_Ensembles.
    split => y H0.
    +inversion H0.
     inversion H1.
     inversion H3.
     inversion H5.
     inversion H7.
     apply ordered_pair_iff in H6.
     inversion H6.
     apply singleton_eq_iff in H4.
     rewrite -H4.
     rewrite -H10.
     rewrite -H11.
     apply singleton_eq_iff.
     apply H8.
    +split.
     exists y.
     split.
     apply H0.
     split.
     split.
     reflexivity.
     split.
     exists x.
     exists y.
     apply singleton_eq_iff in H0.
     rewrite H0.
     split.
     apply HA.
     split.
     apply HA.
     apply ordered_pair_iff.
     done.
  Qed.
End FunctionDefinition.

Require Export class_set.
Require Export direct_product_theories.