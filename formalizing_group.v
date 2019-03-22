From mathcomp
     Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype ssralg.

Require Import ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section ZtoRing.
  Lemma Zeq_boolP : Equality.axiom Zeq_bool.
  Proof.
    move => x y.
    by apply: (iffP idP); rewrite Zeq_is_eq_bool.
  Qed.

  Definition Z_eqMixin := EqMixin Zeq_boolP.

  Canonical Z_eqType := Eval hnf in EqType _ Z_eqMixin.

  Definition Z_pickle (z : Z) : nat :=
    if (0 <=? z)%Z then
      (Z.abs_nat(z)).*2
    else
      (Z.abs_nat(-z)).*2.+1.

  Definition Z_unpickle (n :nat) : option Z :=
    if (odd n) then
      Some (- (Z.of_nat n.-1./2))%Z
    else
      Some (Z.of_nat n./2).

  About pcancel.

  Lemma Z_pickleK : pcancel Z_pickle Z_unpickle.
  Proof.
    move => z; rewrite /Z_pickle.
    case: ifP => z0;
                   rewrite /Z_unpickle /= odd_double (half_bit_double _ false) Zabs2Nat.id_abs Z.abs_eq ?Z.opp_nonneg_nonpos ?Z.opp_involutive //.
    -by apply: Zle_bool_imp_le.
     +move /Z.leb_nle : z0.
        by move /Znot_le_gt /Z.gt_lt /Z.lt_le_incl.
  Qed.
  
End ZtoRing.