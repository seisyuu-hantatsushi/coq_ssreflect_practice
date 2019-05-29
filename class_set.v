From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Coq.Logic.Decidable. (* Introducing decidable *)
Require Import Coq.Sets.Powerset_Classical_facts.

Notation "x ∈ X" := (In _ X x) (right associativity, at level 48).
Notation "A ⊂ B" := (Included _ A B) (right associativity, at level 48).
Notation "A ⊊ B" := (Strict_Included _ A B) (right associativity, at level 48).
Notation "A ^c"   := (Complement _ A) (at level 49).
Notation "A ∪ B" := (Union _ A B) (left associativity, at level 50).
Notation "A ∩ B" := (Intersection _ A B) (left associativity, at level 50).
Notation "A \ B"  := (Setminus _ A B) (left associativity, at level 50).

Notation "{||}"  := (Empty_set _).
Notation "{| x |}" := (Singleton _ x).
Notation "{| x , y , .. , z |}" := (Union _ .. (Union _ (Singleton _ x) (Singleton _ y)) .. (Singleton _ z)).

(* Axiom of separation { x;U | P(x) } *)
Inductive SchemaOfSeparation (U:Type) (x:U) (P:U -> Prop): Ensemble U :=
  Definition_of_Schema_Sepatation:
    forall (x0: U), P x0 -> In U (SchemaOfSeparation x P) x0.

Definition OrderedPair (U:Type) (a b : U) := {|{|a|},{|a,b|}|}.

(* Axiom of the Power Set *)
Inductive DirectProduct (U:Type) (X Y:Ensemble U) : Ensemble (Ensemble (Ensemble U)) :=
  Definition_of_DirectProduct:
    forall (Z: Ensemble (Ensemble U)),
      (exists x:U, exists y:U, (x ∈ X /\ y ∈ Y /\ Z = {|{|x|},{|x,y|}|})) ->
      In (Ensemble (Ensemble U)) (DirectProduct X Y) Z.

(* 𝔓:Unicode 1D513 *)
Notation "𝔓( X )" := (@Power_set _ X) (at level 47).

Notation "X × Y" := (@DirectProduct _ X Y) (at level 49).
Notation "(| a , b |)" := (@OrderedPair _ a b) (at level 48).

Inductive Pr1 {U:Type} (XY: Ensemble (Ensemble (Ensemble U))) : Ensemble U :=
| pr1_accessor: forall (x:U), (exists y:U, (|x,y|) ∈ XY) ->  Pr1 XY x.

Inductive Pr2 {U:Type} (XY: Ensemble (Ensemble (Ensemble U))) : Ensemble U :=
| pr2_accessor: forall (y:U), (exists x:U, (|x,y|) ∈ XY) ->  Pr2 XY y.

Definition Family_of_Sets {K U:Type} := K -> (Ensemble U).

Definition SingleValued {U:Type} (A : Ensemble (Ensemble (Ensemble U))) :=
  forall (x y z:U), (|x,y|) ∈ A /\ (|x,z|) ∈ A -> y = z.

Section Class_Set.

  Variable U:Type.

  Lemma eq_iff: forall (x y:U), x = y <-> y = x.
  Proof.
  +move => x y.
   rewrite /iff.
   split; move => H; rewrite H; reflexivity.
  Qed.

  Lemma singleton_eq_iff: forall (x y : U), x ∈ {|y|} <-> x = y.
  Proof.
    +move => x y.
     rewrite /iff.
     split => H.
     (* x ∈ {|y|} -> x = y *)
     ++apply eq_sym.
       apply Singleton_inv.
       apply H.
     (* x = y -> x ∈ {|y|} *)
     ++rewrite H.
       apply Singleton_intro.
       reflexivity.
  Qed.

  Lemma eq_singleton_eq_element_iff: forall (x y : U), {|x|} = {|y|} <-> x = y.
  Proof.
    +move => x y.
     rewrite /iff.
     split => H.
     (* {|x|} = {|y|} -> x = y *)
     ++apply Singleton_inv.
       rewrite H.
       apply singleton_eq_iff.
       reflexivity.
     (* x = y -> {|x|} = {|y|} *)
     ++rewrite H.
       reflexivity.
  Qed.

  Theorem theorem_of_pairing: forall (x y z:U), x ∈ {|y,z|} <-> x = y \/ x = z.
  Proof.
    +move => x y z.
     rewrite /iff.
     split.
     (* x ∈ {|y,z|} -> x = y \/ x = z. *)
     ++case => w H.
       left.
       apply singleton_eq_iff.
       apply H.
       right.
       apply singleton_eq_iff.
       apply H.
     (*  x = y \/ x = z -> x ∈ {|y,z|} *)
     ++case => H; rewrite H.
       left.
       reflexivity.
       right.
       reflexivity.
  Qed.

End Class_Set.

Export Coq.Sets.Powerset_Classical_facts.
Export Coq.Logic.Decidable.