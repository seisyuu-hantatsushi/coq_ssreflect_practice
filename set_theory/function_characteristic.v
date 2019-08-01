From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import function.

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