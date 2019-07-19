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
    forall (x y:U), (y = f x /\ (|x,y|) ∈ A × B) -> (|x,y|) ∈ GraphOfMap A B f.

Definition Mapping {U:Type} (f : Ensemble (Ensemble (Ensemble U))) (A:Ensemble U) := 
  forall (x:U), x ∈ A /\ (x ∈ A -> exists y:U, ((|x,y|) ∈ f)).

Inductive DomainOfMap {U:Type} (f:Ensemble (Ensemble (Ensemble U))) : Ensemble U :=
| Definition_of_DomainOfMap: forall (x:U), x ∈ Pr1 f -> x ∈ DomainOfMap f.

Inductive ImageOfMap {U:Type} (f:Ensemble (Ensemble (Ensemble U))) (C:Ensemble U) : Ensemble U :=
| Definition_of_ImageOfMap: forall (y:U), (exists x:U, x ∈ C /\ (|x,y|) ∈ f) -> y ∈ ImageOfMap f C.

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
  move : (HA x) => HAx.
  inversion HAx as [HAx0 HAx1].
  move => HDx.
  apply HAx0.
  move : (HA x) => HAx.
  inversion HAx as [HAx0 HAx1].
  move => H0.
  split.
  split.
  apply HAx1.
  apply H0.
Qed.

(* Proofing uniqueness of function *)
Goal forall (A B:Ensemble U) (f: U -> U) (F:Ensemble (Ensemble (Ensemble U))) (x y z:U),
    F = GraphOfMap A B f /\ Mapping F A -> ((|x,y|) ∈ F /\ (|x,z|) ∈ F -> y = z).
Proof.
  move => A B f F x y z H.
  inversion H as [HF HM].
  rewrite HF.
  case => [HFl HFr].
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
  inversion H as [HF HM].
  move => x HxDF.
  inversion HxDF.
  inversion H0.
  inversion H2 as [y].
  exists y.
  unfold unique.
  split.
  apply /Extensionality_Ensembles.
  split => y'.
  move => H5.
  apply singleton_eq_iff in H5.
  split.
  exists x.
  split.
  apply singleton_eq_iff.
  reflexivity.
  rewrite H5.
  apply H4.
  move => H5.
  inversion H5.
  inversion H6 as [x'].
  inversion H8.
  rewrite HF in H10.
  inversion H10 as [x'' y''].
  rewrite HF in H4.
  inversion H4 as [x''' y'''].
  apply ordered_pair_iff in H14.
  inversion H14.
  inversion H11.
  inversion H13.
  apply singleton_eq_iff in H9.
  rewrite -H9 in H15.
  