From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import function.

Section FunctionCharacteristic.

  Variable U:Type.
  Variables one zero: U.
  Variables a b c d: U.

  Definition A := {|a,b,c|}.

  Check In U A a.

  Goal In U A a.
  Proof.
    unfold In.
    unfold A.
    left.
    left.
    apply singleton_eq_iff.
    reflexivity.
  Qed.

  Check In U A a.
  Check (forall (X:Ensemble U) (x:U), {In U X x} + {~In U X x}).

  Axiom in_set_dec: forall (X:Ensemble U) (x:U), {In U X x} + {~In U X x}.

  Definition c_fun (X:Ensemble U) (x:U) : U :=
    match in_set_dec X x with
    | left _ => one
    | right _ => zero
    end.

  Definition cast_fun (X:Ensemble U) (x:U) : nat :=
    match in_set_dec X x with
    | left _ => 1
    | right _ => 0
    end.

  Goal c_fun A a = one.
  Proof.
    unfold c_fun.
    destruct (in_set_dec A a).
    reflexivity.
    move : n.
    case.
    left.
    left.
    apply singleton_eq_iff.
    reflexivity.
  Qed.

  Goal a <> d /\ b <> d /\ c <> d -> c_fun A d = zero.
  Proof.
    case => Had [Hbd Hcd].
    unfold c_fun.
    destruct (in_set_dec A d) as [H|H].
    have: ~d ∈ A.
    unfold A.
    unfold not.
    move => H0.
    inversion H0.
    inversion H1.
    apply singleton_eq_iff in H3.
    apply eq_sym in H3.
    move: H3.
    apply Had.
    apply singleton_eq_iff in H3.
    apply eq_sym in H3.
    move: H3.
    apply Hbd.
    apply singleton_eq_iff in H1.
    apply eq_sym in H1.
    move: H1.
    apply Hcd.
    case.
    apply H.
    reflexivity.
  Qed.
End FunctionCharacteristic.
