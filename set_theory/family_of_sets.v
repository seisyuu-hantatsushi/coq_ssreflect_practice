From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import function.

Definition IndexedFunction {U:Type} := U -> U.

Inductive IndexedSet {U:Type} (I:IndexedFunction) (i:U) : Ensemble U :=
| Definition_of_IndexedSets: forall(x:U), i = I x -> x ∈ IndexedSet I i.

Section Try.
  Variable U:Type.
  Variable IndexedF : U -> U.
  Definition Xi := IndexedSet IndexedF.
 
End Try.

(*
Inductive FamilyOfSets {U:Type} (X:Ensemble U) (IndexedF:IndexedFunction) (I:Ensemble U): Ensemble (Ensemble U) :=
  | Defition_of_FamilyOfSets: forall (i:U), i ∈ I -> (IndexedSet X IndexedF i) ∈ FamilyOfSets X IndexedF I. *)

(* ⎯ : Unicode 23AF (HORIZONTAL LINE EXTENSION) *)
Notation "X ⎯ { i }" := (X i) (at level 45).
Notation "{ X ⎯ ( F , I ) }" := (FamilyOfSets X F I) (at level 45).

Section FamilyOfSets.
  Variable U:Type.
  Variable X I:Ensemble U.
  Variable IndexedF: U -> U.



  
End FamilyOfSets.
