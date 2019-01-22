From mathcomp
     Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict  Implicit.
Import Prenex Implicits.

Definition mySet (M : Type) := M -> Prop.
Definition belong {M : Type} (A : mySet M) (x : M) :
  Prop := A x.

Notation "x ∈ A" := (belong A x) (at level 11).

Axiom axiom_mySet : forall (M :Type) (A : mySet M),
    forall (x : M), (x ∈ A) \/ ~(x ∈ A).

Definition myEmptySet  {M : Type} : mySet M := fun _ => False.
Definition myMotherSet {M : Type} : mySet M := fun _ => True.

Definition mySub {M} :=
  fun (A B : mySet M) => (forall (x : M), (x ∈ A) -> (x ∈ B)).
Notation "A ⊂ B" := (mySub A B) (at level 11).

Section Relation_Of_Inclustion.
  Variable M : Type.

  Lemma Sub_Mother (A : mySet M) : A ⊂ myMotherSet.
  Proof. by []. Qed.

  Lemma Sub_Empty (A : mySet M) : myEmptySet ⊂ A.
  Proof. by []. Qed.

  Lemma rfl_Sub (A : mySet M) : (A ⊂ A).
  Proof. by []. Qed.

  Lemma transitive_Sub (A B C : mySet M):
    (A ⊂ B) -> (B ⊂ C) -> (A ⊂ C).
  Proof.
    move => H1 H2 t H3.
    apply: H2.
    apply: H1.
    apply: H3.
  Qed.

End Relation_Of_Inclustion.

Definition eqmySet {M : Type} :=
    fun (A B : mySet M) => (A ⊂ B /\ B ⊂ A).
Axiom axiom_ExteqmySet : forall {M :Type} (A B : mySet M), eqmySet A B -> A = B.

Section equal_sign.
  Variable Mother : Type.

  Lemma rfl_eqS (A : mySet Mother) : A = A.
  Proof. by []. Qed.

  Lemma sym_eqS (A B : mySet Mother) : A = B -> B = A.
  Proof.
    move => H.
    rewrite H.
    apply rfl_eqS.
  Qed.
End equal_sign.
