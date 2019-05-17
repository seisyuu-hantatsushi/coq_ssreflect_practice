From mathcomp Require Import ssreflect.

Require Import Coq.Logic.Decidable. (* Introducing decidable *)
Require Import Coq.Sets.Powerset_Classical_facts.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module SetNotations.

  Notation "x ∈ X" := (In _ X x) (at level 48).
  Notation "A ⊂ B" := (Included _ A B) (at level 48).
  Notation "A ^c"   := (Complement _ A) (at level 49).
  Notation "A ∪ B" := (Union _ A B) (at level 50).
  Notation "A ∩ B" := (Intersection _ A B) (at level 50).
  Notation "A \ B"  := (Setminus _ A B) (at level 50).

  Notation "{||}"  := (Empty_set _).
  Notation "{| x |}" := (Singleton _ x).
  Notation "{| x , y , .. , z |}" := (Union _ .. (Union _ (Singleton _ x) (Singleton _ y)) .. (Singleton _ z)).

  (* Axiom of separation { x;U | P(x) } *)
  Inductive SchemaOfSeparation (U:Type) (x:U) (P:U -> Prop): Ensemble U :=
    Definition_of_Schema_Sepatation:
      forall (x0: U), P x0 -> In U (SchemaOfSeparation x P) x0.

  Notation "{| x | P |}" :=  (SchemaOfSeparation x P).

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

End SetNotations.

Export Coq.Logic.Decidable.
Export Coq.Sets.Powerset_Classical_facts.

Import SetNotations.

Lemma eq_iff: forall (U:Type) (x y:U), x = y <-> y = x.
Proof.
  +move => U x y.
   rewrite /iff.
   split; move => H; rewrite H; reflexivity.
Qed.

Lemma singleton_eq_iff: forall (U:Type) (x y : U), x ∈ {|y|} <-> x = y.
Proof.
  +move => U x y.
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

Lemma eq_singleton_eq_element_iff: forall (U:Type) (x y : U), {|x|} = {|y|} <-> x = y.
Proof.
  +move => U x y.
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

Theorem theorem_of_pairing: forall (U:Type) (x y z:U), x ∈ {|y,z|} <-> x = y \/ x = z.
Proof.
  +move => U x y z.
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

Section Validation.
  Import SetNotations.
  Variable U:Type.
  Variable a b c :U.

  Goal forall (x:U), {| x | (fun x => x = a \/ x = b) |} = {| a, b |}.
  Proof.
    move => x.
    apply: Extensionality_Ensembles.
    split => y.
    case => [z [H1|H1]]; rewrite H1.
    left.
    reflexivity.
    right.
    reflexivity.
    case => z H1; split.
    left.
    apply singleton_eq_iff.
    apply H1.
    right.
    apply singleton_eq_iff.
    apply H1.
  Qed.

  Goal {| a , a |} = {| a |}.
  Proof.
    apply: Extensionality_Ensembles.
    split => x.
    -case; move => y; apply.
    -left.
     apply H.
  Qed.

  Goal {||} ⊂ {| a , b , c |}.
  Proof.
    move => x.
    case.
  Qed.

  Goal {| a, b |} ⊂ {| a , b , c |}.
  Proof.
    move => x.
    case => y H; left.
    -left.
     apply H.
    -right.
     apply H.
  Qed.

  Goal forall (A:Ensemble U), A = A ∪ {||}.
  Proof.
    move => A.
    apply: Extensionality_Ensembles.
    split => x.
    -left.
     apply H.
    -case => y.
     apply.
     case.
  Qed.

  Goal forall (A:Ensemble U), {||} = A ∩ {||}.
  Proof.
    move => A.
    apply: Extensionality_Ensembles.
    split => x.
    -move => H1.
     split.
     move: H1.
     case.
     apply H1.
     case => y H1.
     apply.
  Qed.

  Goal (fun x => x = a \/ x = b \/ x = c) = {| a , b , c |}.
  Proof.
    apply: Extensionality_Ensembles.
    split => x.
    -case => H.
    --left.
      left.
      rewrite H.
      reflexivity.
      inversion H.
    --left.
      right.
      rewrite H0.
      reflexivity.
    --right.
      rewrite H0.
      reflexivity.
    -case => y.
     case => z H1.
     --left.
       apply singleton_eq_iff.
       apply H1.
     --right.
       left.
       apply singleton_eq_iff.
       apply H1.
     -move => H1.
      right.
      right.
      apply singleton_eq_iff.
      apply H1.
  Qed.

End Validation.
