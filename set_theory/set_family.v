From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import function.

Definition IndexedFunction {U:Type} := U -> Prop.

Inductive FamilySet {U:Type} (X:Ensemble U) (I:IndexedFunction) (i:U) : Ensemble U :=
| Definition_of_FamilySet: forall(x:U), I i /\ x ∈ X -> x ∈ FamilySet X I i.

Section SetFamily.
  Variable U:Type.
  

  
End SetFamily.