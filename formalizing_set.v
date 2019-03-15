
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

Definition myEmptySet  {M : Type} : mySet M := fun _ => False.
Definition myMotherSet {M : Type} : mySet M := fun _ => True.

Definition mySub {M} :=
  fun (A B : mySet M) => (forall (x : M), (x ∈ A) -> (x ∈ B)).
Notation "A ⊂ B" := (mySub A B) (at level 11).

Section Relation_Of_Inclustion.
  Variable M : Type.

  Lemma Sub_Mother (A : mySet M) : A ⊂ myMotherSet.
  Proof. by []. Qed.

  Lemma Sub_Empty (A : mySet M) : myEmptySet ⊂ A.
  Proof. by []. Qed.

  Lemma rfl_Sub (A : mySet M) : (A ⊂ A).
  Proof. by []. Qed.

  Lemma transitive_Sub (A B C : mySet M):
    (A ⊂ B) -> (B ⊂ C) -> (A ⊂ C).
  Proof.
    move => H1 H2 t H3.
    apply: H2.
    apply: H1.
    apply: H3.
  Qed.

End Relation_Of_Inclustion.

Definition eqmySet {M : Type} :=
    fun (A B : mySet M) => (A ⊂ B /\ B ⊂ A).
Axiom axiom_ExteqmySet : forall {M :Type} (A B : mySet M), eqmySet A B -> A = B.

Section equal_sign.
  Variable Mother : Type.

  Lemma rfl_eqS (A : mySet Mother) : A = A.
  Proof. by []. Qed.

  Lemma sym_eqS (A B : mySet Mother) : A = B -> B = A.
  Proof.
    move => H.
    rewrite H.
    apply rfl_eqS.
  Qed.
End equal_sign.

Definition myComplement {M :Type} (A : mySet M) : mySet M :=
  fun (x : M) => ~(A x).
Notation "A ^c" := (myComplement A) (at level 11).

Definition myCup {M : Type} (A B : mySet M) : mySet M :=
  fun (x : M) => (x ∈ A) \/ (x ∈ B).

Notation "A ∪ B" := (myCup A B) (at level 11).

Definition myCap {M : Type} (A B : mySet M) : mySet M :=
  fun (x : M) => (x ∈ A) /\ (x ∈ B).

Notation "A ∩ B" := (myCap A B) (at level 11).

Definition mySetDiff {M : Type} (A B : mySet M) : mySet M :=
  fun (x : M) => (x ∈ A) /\ (x ∈ (myComplement B)).

Notation "A \ B" := (mySetDiff A B) (at level 11).

Section Set_Operation.
  Variable M : Type.

  Lemma cEmpty_Mother: (@myEmptySet M)^c = myMotherSet.
  Proof.
    apply: axiom_ExteqmySet.
    rewrite /eqmySet.
    apply conj.
    rewrite /mySub /myComplement //.
    rewrite /mySub.
    move => x Hfull.
    rewrite /belong.
    rewrite /myMotherSet /belong in Hfull.
    rewrite /myComplement /myEmptySet.
      by [].
  Qed.

  Lemma cc_cancel (A : mySet M) : (A^c)^c = A.
  Proof.
    apply: axiom_ExteqmySet; rewrite /eqmySet.
    apply: conj.
    rewrite /mySub /myComplement => x H //.
    move : (axiom_mySet A x); by case.
    rewrite /mySub /myComplement => x H //.
  Qed.

  Lemma cMother_Empty: (@myMotherSet M)^c = myEmptySet.
  Proof.
    rewrite -cEmpty_Mother.
    rewrite cc_cancel.
    by [].
  Qed.

  Lemma myUnionCompMother (A : mySet M) : A ∪ (A^c) = myMotherSet.
  Proof.
    apply: axiom_ExteqmySet.
    rewrite /eqmySet /mySub; apply: conj => [x | x H1].
    -by case.
    -case: (axiom_mySet A x).
     move => HAx.
     apply: or_introl; apply HAx.
     move => HAx.
     by apply: or_intror.
  Qed.

  Lemma myIntersectionCompEmpty (A : mySet M) : A ∩ (A^c) = myEmptySet.
  Proof.
    apply: axiom_ExteqmySet.
    rewrite /eqmySet /mySub.
    split => x.
    case => HA HnA.
    rewrite /myEmptySet.
    apply: HnA HA.
    by [].
  Qed.

  Lemma myCupUnionRule (A B C : mySet M) : (A ∪ B) ∪ C = A ∪ (B ∪ C).
  Proof.
    apply: axiom_ExteqmySet.
    rewrite /eqmySet.
    apply conj => x [H1 | H2].
    -case H1 => t.
     apply: or_introl; apply t.
     apply: or_intror; apply: or_introl; apply t.
     apply: or_intror; apply: or_intror; apply H2.
     apply: or_introl; apply: or_introl; apply H1.
    -case H2 => t.
     apply: or_introl; apply: or_intror; apply t.
     apply: or_intror; apply t.
  Qed.

  Lemma myCapUnionRule (A B C: mySet M) : A ∩ (B ∩ C) = (A ∩ B) ∩ C.
  Proof.
    apply: axiom_ExteqmySet.
    rewrite /eqmySet.
    apply: conj => x [H1 H2].
    apply conj. apply conj.
    apply: H1.
    move: H2; by case.
    move: H2; by case.
    apply: conj.
    move: H1; by case.
    apply: conj.
    move: H1; by case.
    by [].
  Qed.

  Lemma mySetCommutativeCup (A B: mySet M): A ∪ B = B ∪ A.
  Proof.
    apply: axiom_ExteqmySet.
    rewrite /eqmySet.
    split => t.
    case => H1.
      by right. by left.
    case => H1.
      by right. by left.
  Qed.

  Lemma mySetCommutativeCap (A B: mySet M): A ∩ B = B ∩ A.
  Proof.
    apply: axiom_ExteqmySet.
    rewrite /eqmySet.
    split => t.
    case => H1 H2.
    split; by[].
    case => H1 H2.
    split; by [].
  Qed.

  Lemma myCapDistributeRule (A B C: mySet M): A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C).
  Proof.
    apply: axiom_ExteqmySet.
    rewrite /eqmySet.
    split; move => t.
    case => H1.
    case => H2.
    left; split; by [].
    right; split; by [].
    case; case => H1 H2.
    split. by [].
    left. by [].
    split. by [].
    right. by[].
  Qed.

  Lemma mySetDemorgan_1 (A B: mySet M): (A ∪ B)^c = (A^c) ∩ (B^c).
  Proof.
    apply: axiom_ExteqmySet.
    rewrite /eqmySet.
    split.
    move => x HABc.
    split.
    rewrite /myComplement /not.
    move => H1.
    apply: HABc.
    left.
    apply H1.
    rewrite /myComplement /not.
    move => H1.
    apply: HABc.
    by right.
    move => x.
    case => H1 H2 H3.
    apply: H1.
    by case: H3.
  Qed.

  Lemma mySetDemorgan_2 (A B: mySet M): (A ∩ B)^c = (A^c) ∪ (B^c).
    move: (cc_cancel ((A^c) ∪ (B^c))) (cc_cancel (A ∩ B)).
    move => Hcc_cancel_or Hcc_cancel_and.
    apply: axiom_ExteqmySet.
    rewrite /eqmySet.
    split.
    rewrite -Hcc_cancel_and -Hcc_cancel_or.
    rewrite mySetDemorgan_1.
    rewrite Hcc_cancel_and.
    rewrite cc_cancel cc_cancel.
      by [].
    rewrite -Hcc_cancel_or.
    rewrite mySetDemorgan_1.
    rewrite cc_cancel cc_cancel.
      by [].
  Qed.

  Lemma mySetDiffSelfEmpty (A: mySet M): A \ A = myEmptySet.
  Proof.
    rewrite -(myIntersectionCompEmpty A).
    by rewrite /mySetDiff.
  Qed.

  Lemma mySetDiffEq (A B: mySet M): B \ A = A^c ∩ B.
  Proof.
    rewrite -mySetCommutativeCap.
    by rewrite /mySetDiff /myCap.
  Qed.

  Lemma mySetDiffComplement (A B: mySet M): (B \ A)^c = A ∪ (B^c).
  Proof.
    move: (cc_cancel (A ∪ (B^c))).
    move => H1.
    rewrite -H1.
    rewrite mySetDemorgan_1 cc_cancel mySetDiffEq.
      by [].
  Qed.

  Lemma mySetDiffDistCap (A B C: mySet M): C \ (A ∩ B) = (C \ A) ∪ (C \ B).
  Proof.
    rewrite mySetDiffEq mySetDemorgan_2.
    rewrite mySetCommutativeCap.
    rewrite myCapDistributeRule.
      by rewrite mySetDiffEq mySetCommutativeCap.
  Qed.

End Set_Operation.

Definition myMap {M1 M2 : Type} (A: mySet M1) (B: mySet M2) (f: M1 -> M2)
           := (forall (x : M1), (x ∈ A) -> ((f x) ∈ B)).
Notation "f |: A |→ B" := (myMap A B f) (at level 11).

(* 逆像の形式化 *)
Definition myInverseImg {M1 M2 : Type} (A: mySet M1) (B: mySet M2) (f: M1 -> M2)
  := (forall (x: M1), ((f x) ∈ B) -> (x ∈ A)).


Definition MapCompsite {M1 M2 M3: Type} (f: M2 -> M3) (g: M1 -> M2): M1 -> M3 := fun (x: M1) => f (g x).

Notation "f ・ g" := (MapCompsite f g) (at level 11).

(* 像の形式化 *)
Definition ImgOf
           {M1 M2 : Type} (f: M1 -> M2)
           {A : mySet M1} {B : mySet M2} (_ : f |: A |→ B) : mySet M2 :=
  fun (y : M2) => (exists (x : M1), y = f x /\ x ∈ A).

(* 単射の形式化 *)
Definition mySetInj {M1 M2 : Type} (f: M1 -> M2) (A : mySet M1) (B : mySet M2)
           (_ : f |: A |→ B) := forall (x y : M1), (x ∈ A) -> (y ∈ A) -> (f x = f y) -> (x = y).
(* 全射の形式化 *)
Definition mySetSur {M1 M2 : Type} (f: M1 -> M2) (A : mySet M1) (B : mySet M2) (_ : f |: A |→ B) :=
           forall (y : M2), (y ∈ B) -> (exists (x : M1), (x ∈ A) -> (f x = y)).
(* 全単射の形式化 *)
Definition mySetBi {M1 M2 : Type} (f: M1 -> M2) (A : mySet M1) (B : mySet M2) (fAB : f |: A |→ B) :=
  (mySetInj fAB) /\ (mySetSur fAB).

Section Mapping.
  Variables M1 M2 M3 : Type.
  Variable f : M2 -> M3.
  Variable g : M1 -> M2.
  Variable A : mySet M1.
  Variable B : mySet M2.
  Variable C : mySet M3.
  Hypothesis gAB : g |: A |→ B.
  Hypothesis fBC : f |: B |→ C.

  Lemma transitive_Inj (fgAC : (f ・ g) |: A |→ C) :
    mySetInj fBC -> mySetInj gAB -> mySetInj fgAC.
  Proof.
    rewrite /mySetInj => Hinjf Hinjg x y HxA HyA H.
    apply: (Hinjg x y HxA HyA).
    apply: (Hinjf (g x) (g y)).
    apply: gAB HxA.
    apply: gAB HyA.
    apply: H.
  Qed.

  Lemma CompoTrans : (f ・ g) |: A |→ C.
  Proof.
    move: gAB fBC.
    rewrite /MapCompsite /myMap => Hab Hbc t Ha.
    move: (Hbc (g t) (Hab t Ha)).
      by [].
  Qed.

  Lemma ImSub : (ImgOf gAB) ⊂ B.
  Proof.
    rewrite /mySub => x; case => x0; case => H1 H2.
    rewrite H1; apply: gAB; apply: H2.
  Qed.

End Mapping.

Section MappingProblem.
  Variables M1 M2 : Type.
  Variable f : M1 -> M2.
  Variables A A1 A2 : mySet M1.
  Variables B B1 B2 B3 B4 B5 : mySet M2.
  Hypothesis fAB : f |: A |→ B.
  Hypothesis fA1B1 : f |: A1 |→ B1.
  Hypothesis fA2B2 : f |: A2 |→ B2.
  Hypothesis fA1cupA2_B3 : f |: (A1 ∪ A2) |→ B3.
  Hypothesis fA1capA2_B4 : f |: (A1 ∩ A2) |→ B4.
  Hypotheses fAdiffA1_B5: f |: (A \ A1) |→ B5.

  (* A1 ⊂ A2 ならば f(A1) ⊂ f(A2) *)
  Lemma ImgSub: A1 ⊂ A2 -> (ImgOf fA1B1) ⊂ (ImgOf fA2B2).
  Proof.
    rewrite /mySub => HS.
    move => x.
    case => x0; case => H1 H2.
    rewrite /ImgOf.
    exists x0.
    split.
    apply: H1.
    apply: HS.
    apply: H2.
  Qed.

  (* f(A1 ∪ A2) = f(A1) ∪ f(A2) *)
  Lemma ImgCup: (ImgOf fA1cupA2_B3) = (ImgOf fA1B1) ∪ (ImgOf fA2B2).
  Proof.
    apply: axiom_ExteqmySet.
    rewrite /eqmySet.
    split.
    rewrite /mySub /ImgOf.
    move => x.
    case => x0.
    case => H1.
    case => H2.
    +left.
     exists x0; split.
     apply: H1.
     apply: H2.
    +right.
     exists x0; split.
     apply: H1.
     apply: H2.
    rewrite /mySub /ImgOf.
    move => x.
    case; case => x0; case => fx H1; exists x0.
    split.
    apply: fx.
    left; by [].
    split.
    apply: fx.
    right; by[].
  Qed.

  (* f(A1 ∩ A2) ⊂ f(A1) ∩ f(A2) *)
  Lemma ImgCap: (ImgOf fA1capA2_B4) ⊂ ((ImgOf fA1B1) ∩ (ImgOf fA2B2)).
  Proof.
    rewrite /mySub.
    move => x.
    case => x0.
    case => fx.
    case => H1 H2.
    rewrite /ImgOf.
    split; exists x0.
    split.
    apply: fx.
    apply: H1.
    split.
    apply: fx.
    apply: H2.
  Qed.

  (* A1 ⊂ A2 -> A2^c ⊂ A1^c *)
  Lemma Contraposition: A1 ⊂ A2 -> (A2^c) ⊂ (A1^c).
  Proof.
    rewrite /mySub /myComplement /not /belong.
    move => H1 x H2 H3.
    apply /H2 /(H1 x) /H3.
  Qed.

  (* A1 ⊂ A -> f(A)\f(A1) ⊂ f(A\A1) *)
  Lemma diffImgOf: A1 ⊂ A -> (ImgOf fAB) \ (ImgOf fA1B1) ⊂ (ImgOf fAdiffA1_B5).
  Proof.
    rewrite /mySub /mySetDiff /belong /ImgOf /myComplement /not.
    move => H1 x2.
    case.
    case.
    move => x1.
    case.
    move => H2 H3 H4.
    exists x1.
    split.
    apply /H2.
    split.
    apply /H3.
    move => H5.
    apply /H4.
    exists x1.
    split.
    apply /H2.
    apply /H5.
  Qed.
  
End MappingProblem.

Variable M :finType.

Definition p2S (pA: pred M) : mySet M :=
  fun (x : M) => if (x \in pA) then True else False.

Notation "\{ x 'in' pA \}" := (p2S pA).

Section finiteSet_UsingFintype.
  Lemma Mother_predT : myMotherSet = \{ x in M \}.
  Proof.
      by [].
  Qed.

  Lemma myFinBelongP (x : M) (pA : pred M): reflect (x ∈ \{ x in pA \}) (x \in pA).
  Proof.
    rewrite /belong /p2S; apply/ (iffP idP) => H1.
    -by rewrite (_ : (x \in pA) = true).
     -+have testH : (x \in pA) || ~~(x \in pA).
     set t := x \in pA.
       by case: t.
     move: testH.
     case/orP => [| Harg]; first by [].
     rewrite (_ : (x \in pA) = false) in H1; first by [].
     by apply : negbTE.
  Qed.

  Lemma myFinSubsetP (pA pB : pred M) :
    reflect (\{ x in pA \} ⊂ \{ x in pB \}) (pA \subset pB).
  Proof.
    rewrite /mySub; apply/ (iffP idP) => H.
    -move => x /myFinBelongP => H2.
     apply /myFinBelongP.
     move: H => /subsetP.
       by rewrite /sub_mem; apply.
    -apply/ subsetP.
     rewrite /sub_mem=> x /myFinBelongP => HpA.
       by apply/ myFinBelongP; apply H.
  Qed.

  Lemma Mother_Sub (pA : pred M) :
    myMotherSet ⊂ \{ x in pA \} -> forall x, x ∈ \{ x in pA \}.
  Proof.
    rewrite Mother_predT => /myFinSubsetP => H x; apply /myFinBelongP.
      by apply: predT_subset.
  Qed.

  Lemma transitive_Sub' (pA pB pC : pred M):
    \{ x in pA \} ⊂ \{ x in pB \} ->
    \{ x in pB \} ⊂ \{ x in pC \} ->
    \{ x in pA \} ⊂ \{ x in pC \}.
  Proof.
    move /myFinSubsetP => HAB /myFinSubsetP => HBC.
    apply /myFinSubsetP /(subset_trans HAB HBC).
  Qed.

  Lemma transitive_Sub'' (pA pB pC : pred M):
    \{ x in pA \} ⊂ \{ x in pB \} ->
    \{ x in pB \} ⊂ \{ x in pC \} ->
    \{ x in pA \} ⊂ \{ x in pC \}.
  Proof.
    apply: transitive_Sub.
  Qed.
End finiteSet_UsingFintype.