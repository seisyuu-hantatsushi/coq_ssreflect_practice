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

End Set_Operation.
