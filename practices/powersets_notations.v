From mathcomp Require Import ssreflect.

Require Import set_notations.

Import SetNotations.
Export SetNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module PowersetNotations.

  (* {C ∈ Power(X)| P(C)}, P(C) = A ⊂ C *)
  Inductive sigPE (U:Type) (X:Ensemble U) (P:Ensemble U -> Prop) :
    Ensemble (Ensemble U) :=
    Definition_of_Intensive_Power_set:
      forall C:Ensemble U, P C ->
                           (Included U C X -> In (Ensemble U) (sigPE X P) C).

  Notation "{ X |^ P }" := (sigPE X P).

End PowersetNotations.