From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Coq.Sets.Classical_sets.

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