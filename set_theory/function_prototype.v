From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import logic_theories.
Require Import class_set.
Require Import direct_product_theories.

Definition FunctionOfMap {U:Type} := U -> U.

Inductive GraphOfMap {U:Type} (A B:Ensemble U) (f:FunctionOfMap) : Ensemble (Ensemble (Ensemble U)) :=
| Definition_of_GraphOfMap:
    forall (x y:U), (y = f x) /\ (|x,y|) ∈ A × B -> (|x,y|) ∈ GraphOfMap A B f.

Definition Mapping {U:Type} (f : Ensemble (Ensemble (Ensemble U))) (A:Ensemble U) := 
  forall (x:U), x ∈ A -> exists y:U, ((|x,y|) ∈ f).

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

Variable U : Type.

Goal forall (A B:Ensemble U) (f: U -> U) (F:Ensemble (Ensemble (Ensemble U))),
    F = GraphOfMap A B f /\ Mapping F A -> DomainOfMap F = A.
Proof.
  move => A B f F.
  case => H.
  unfold Mapping.
  move => HA.
  apply /Extensionality_Ensembles.
  split => x.
  move : (HA x) => HAx HxDF.
  inversion HxDF.
  inversion H0.
  inversion H2 as [z].
  rewrite H in H4.
  inversion H4 as [x' z'].
  inversion H5.
  rewrite H6 in H8.
  apply ordered_pair_in_direct_product_iff_and in H8.
  inversion H8.
  apply H9.
  move : (HA x) => HAx.
  move => HA'.
  split.
  split.
  apply HAx.
  apply HA'.
Qed.

(* Proofing uniqueness of function *)
Goal forall (A B:Ensemble U) (f: U -> U) (F:Ensemble (Ensemble (Ensemble U))) (x y z:U),
    F = GraphOfMap A B f /\ Mapping F A -> ((|x,y|) ∈ F /\ (|x,z|) ∈ F -> y = z).
Proof.
  move => A B f F x y z H.
  inversion H as [HF HFM].
  rewrite HF.
  case => [HFl HFr].
  move: (HFM x) => HFMx.
  inversion HFl.
  inversion H1.
  apply ordered_pair_iff in H0.
  inversion H0.
  inversion HFr.
  inversion H7.
  apply ordered_pair_iff in H6.
  inversion H6.
  rewrite H4 in H2.
  rewrite H5 in H2.
  rewrite H10 in H8.
  rewrite H11 in H8.
  rewrite H2.
  rewrite H8.
  reflexivity.
Qed.

Goal forall (A B:Ensemble U) (f:U -> U) (F:Ensemble (Ensemble (Ensemble U))),
    F = GraphOfMap A B f /\ Mapping F A -> (forall (x:U), x ∈ DomainOfMap F -> exists! y, {|y|} = ImageOfMap F {|x|}).
Proof.
  move => A B f F H.
  inversion H as [HF HFM].
  move => x HxDF.
  inversion HxDF.
  inversion H0.
  inversion H2 as [y].
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
   apply H4.
  +move => H5.
   apply singleton_eq_iff.
   unfold Mapping in HFM.
   move: (HFM x) => HFMx.
   inversion H5.
   inversion H6 as [x'].
   inversion H8.
   rewrite HF in H10.
   inversion H10 as [x'' y''].
   apply ordered_pair_iff in H12.
   inversion H12.
   rewrite HF in H4.
   inversion H4 as [x''' y'''].
   apply ordered_pair_iff in H16.
   inversion H16.
   inversion H11.
   inversion H15.
   apply singleton_eq_iff in H9.
   rewrite H9 in H13.
   rewrite H13 in H19.
   rewrite H14 in H19.
   rewrite H17 in H21.
   rewrite H18 in H21.
   rewrite H19.
   rewrite H21.
   reflexivity.
  +move => x' H5.
   apply Extension in H5.
   unfold Same_set in H5.
   unfold Included in H5.
   inversion H5.
   move: (H7 y) => H7y.
   apply singleton_eq_iff.
   apply H7y.
   split.
   exists x.
   split.
   apply singleton_eq_iff.
   reflexivity.
   apply H4.
Qed.

Goal forall (A B C D:Ensemble U) (f g: U -> U) (F G:Ensemble (Ensemble (Ensemble U))),
    F = GraphOfMap A B f /\ Mapping F A /\ G = GraphOfMap C D g /\ Mapping G C /\ B ⊂ C -> DomainOfMap (CompoundMap G F) = A /\ RangeOfMap (CompoundMap G F) ⊂ D.
Proof.
  move => A B C D f g F G.
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
