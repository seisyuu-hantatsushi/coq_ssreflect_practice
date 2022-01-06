From mathcomp Require Import ssreflect.

Require Import Coq.Arith.Peano_dec.

Check eq_nat_dec.

Eval compute in eq_nat_dec 1 1.
Eval compute in eq_nat_dec 1 0.

About eq_nat_dec.
Check eq_nat_dec.
Check eq_nat_dec 1 1.

Definition test_func (n m:nat) : nat :=
  match eq_nat_dec n m with
  | left _ => 1
  | right _ => 0
  end.

Eval compute in test_func 1 1. (* result 1 *)
Eval compute in test_func 1 0. (* result 0 *)

