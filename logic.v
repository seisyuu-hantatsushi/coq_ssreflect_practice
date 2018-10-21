From mathcomp
     Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Logic.
  Hypothesis ExMidLaw : forall P : Prop, P \/ ~P.

  Lemma notnotEq (P : Prop): ~~P -> P.
  Proof.
    move => HnotnotP.
    move : (ExMidLaw (~P)).
    case.
    -by move /HnotnotP.
    -by case : (ExMidLaw P).
  Qed.

  Lemma DeMorgran_1 (A B : Prop) : ~(A /\ B) -> ~A \/ ~B.
  Proof.
    move => notAandB.
    apply : notnotEq.
    move => HnotnotNAorNB.
    apply : notAandB.
    apply : conj.
    apply : notnotEq.
    move => HnotnotA.
    apply : HnotnotNAorNB.
    apply : or_introl.
    apply : HnotnotA.
    apply : notnotEq.
    move => HnotnotB.
    apply : HnotnotNAorNB.
    apply : or_intror.
    apply : HnotnotB.
  Qed.

  Lemma DeMorgran_2 (A B : Prop) :  ~A \/ ~B -> ~(A /\ B).
  Proof.
    move => Hor. (* -> 導入 *)
    move => Hand. (* not 導入 *)
    move : Hor. (* ~A \/ ~Bを仮定する *)
    case. (* \/の除去 AとBの場合分け *)
    move => notA.
    apply notA. (* not の除去 *)
    apply Hand. (* /\の除去 *)
    move => notB.
    apply notB.
    apply Hand.
  Qed.

  Lemma DeMorgran (A B : Prop) : ~(A /\ B) <-> ~A \/ ~B.
  Proof.
    rewrite /iff.
    -apply : conj => notAandB.
     +apply : notnotEq => HnotnotNAorNB.
      apply : notAandB.
      apply : conj.
      *apply : notnotEq => HnotnotA.
       apply : HnotnotNAorNB.
       apply : or_introl.
       apply : HnotnotA.
       apply : notnotEq => HnotnotB.
       apply : HnotnotNAorNB.
       apply : or_intror.
       apply : HnotnotB.
    -move : notAandB => HnotAornotB.
     move => HAandB.
     move : HnotAornotB.
     +case => notA.
      apply : notA.
      apply HAandB.
      move : notA => notB.
      apply : notB.
      apply HAandB.
  Qed.

  Lemma J_DeMorgan_0 (T : Type) (P : T -> Prop):
    ~(exists x, (P x)) -> forall x, ~(P x).
  Proof.
    move => HnotEx.
    move => x0 HPx.
    apply : HnotEx.
    exists x0.
      by [].
  Qed.
  
  Lemma J_DeMorgan_1 (T : Type) (P : T -> Prop):
    ~(forall x, (P x)) -> exists x, ~(P x).
  Proof.
    move => notForAll.
    apply : notnotEq.
    move => HnotnotEP.
    apply : notForAll.
    move => x0.
    apply : notnotEq.
    move => notnotP.
    apply : HnotnotEP.
    exists x0.
      by [].
  Qed.

  Lemma J_DeMorgan_2 (T : Type) (P : T -> Prop):
    (exists x, ~(P x)) -> ~(forall x, (P x)).
  Proof.
    case.
    move => x0 HnotPx0.
    apply : notnotEq.
    move => H1.
    apply : HnotPx0.
    apply : notnotEq.
    move => H2.
    apply : H1.
    move => H3.
    apply : H2.
    apply : H3.
  Qed.

  Lemma J_DeMorgan (T : Type) (P : T -> Prop):
    ~(forall x, (P x)) <-> exists x, ~(P x).
  Proof.
    rewrite /iff.
    apply conj.
    apply : J_DeMorgan_1.
    apply : J_DeMorgan_2.
  Qed.

End Logic.


