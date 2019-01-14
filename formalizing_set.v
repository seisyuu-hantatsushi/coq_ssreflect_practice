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

