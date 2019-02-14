From mathcomp
     Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section using_finset_lib.
  From mathcomp
       Require Import finset.
  Variable M : finType.

  Lemma demorgan_1 (A B C : {set M}):
    (A :&: B) :|: C = (A :|: C) :&: (B :|: C).
  Proof.
    apply/setP => x.
    rewrite !inE.
    rewrite -orb_andl.
      by [].
  Qed.

  About orb_andl.
  
  Lemma demorgan_2 (A B C : {set M}):
    (A :|: B) :&: C = (A :&: C) :|: (B :&: C).
  Proof.
    apply/setP => x.
    rewrite !inE.
    rewrite -andb_orl.
      by [].
  Qed.
  
End using_finset_lib.