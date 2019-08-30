From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import function.

Inductive SetOfSingleton {U:Type} (M:Ensemble U) : Ensemble (Ensemble U) :=
| Definition_of_SetOfSingleton: forall (a:U), a ∈ M -> {|a|} ∈ SetOfSingleton M.

Section FamilyOfSetsPrototype.
  Variable U:Type.
  Variables X Y I:Ensemble U.

  Lemma element_of_set_of_singleton_is_unique:
    forall (A X: Ensemble U) (a b:U),
      A ∈ SetOfSingleton X -> (a ∈ A /\ b ∈ A -> a = b).
  Proof.
    move => A X' a b H  [Ha Hb].
    inversion H.
    rewrite -H1 in Ha.
    rewrite -H1 in Hb.
    apply singleton_eq_iff in Ha.
    apply singleton_eq_iff in Hb.
    rewrite Ha Hb.
    done.
  Qed.

  Lemma set_of_singleton_cast:
    forall (z:U) (Z:Ensemble U), {|z|} ∈ SetOfSingleton Z <-> z ∈ Z.
  Proof.
    move => z Z.
    rewrite /iff.
    split => H.
    inversion H.
    apply (eq_singleton_eq_element_iff a z) in H0.
    rewrite -H0.
    apply H1.
    split.
    apply H.
  Qed.

  Lemma set_of_singlton_source_set_iff:
    SetOfSingleton X = SetOfSingleton Y <-> X = Y.
  Proof.
    rewrite /iff.
    split => H.
    apply Extension in H.
    inversion H as [HSX HSY].
    apply /Extensionality_Ensembles.
    split => z;rewrite -(set_of_singleton_cast z Y) -(set_of_singleton_cast z X).
    apply HSX.
    apply HSY.
    rewrite H.
    reflexivity.
  Qed.

  Goal forall (i:U)
              (II X:Ensemble (Ensemble U))
              (Xn:Ensemble (Ensemble (Ensemble (Ensemble U))))
              (F:FunctionOfMap (Ensemble U)),
      i ∈ I /\ II=SetOfSingleton I /\ Xn ≔ F ⊦ II ⟼ X -> exists! Xi, {|Xi|} = Xn '' {|{|i|}|}.
  Proof.
    move => i II X0 Xn F [HiI [HII [HXn HXnS]]].
    have L1: exists Xi:Ensemble U, (|{|i|},Xi|) ∈ Xn.
    apply (HXnS {|i|}).
    rewrite HII.
    split.
    done.
    inversion L1 as [Xi].
    exists Xi.
    split.
    apply /Extensionality_Ensembles.
    split => X' H0.
    split.
    exists {|i|}.
    split.
    done.
    apply singleton_eq_iff in H0.
    rewrite H0.
    done.
    rewrite HXn in H.
    inversion H as [I' X0'].
    inversion H0 as [X1' [I1' []]].
    apply singleton_eq_iff in H3.
    rewrite H3 in H4.
    rewrite HXn in H4.
    inversion H4 as [I2' X2' []].
    inversion H1.
    apply ordered_pair_iff in H2.
    inversion H2.
    apply ordered_pair_iff in H8.
    inversion H8.
    rewrite H14 in H6.
    rewrite H13 in H6.
    rewrite H12 in H9.
    rewrite H11 in H9.
    rewrite -H9 in H6.
    apply singleton_eq_iff.
    done.
    move => Xi' H0.
    apply Extension in H0.
    inversion H0.
    apply singleton_eq_iff.
    apply (H2 Xi).
    split.
    exists {|i|}.
    split.
    done.
    apply H.
  Qed.

  (* F:U -> Ensemble U となるような写像を作る *)
  Definition FunctionOfFamilySet := U -> Ensemble U.

  Variable IndexedFunction : Ensemble U -> Ensemble U.
  Definition FunctionOfFamilySetUpCast (i:U) := IndexedFunction {|i|}.

  Inductive GraphOfFamilySets (F:FunctionOfFamilySet) (I:Ensemble U) (XX:Ensemble (Ensemble U)):
    Ensemble (Ensemble (Ensemble (Ensemble U))) :=
  | Definition_of_GraphOfFamilySet: forall (i:U) (Xi:Ensemble U), Xi = F i /\ (|{|i|}, Xi|) ∈ (SetOfSingleton I) × XX -> (|{|i|}, Xi|) ∈ GraphOfFamilySets F I XX.

  Definition MappingFamilyOfSets (Xn:Ensemble (Ensemble (Ensemble (Ensemble U)))) (F:FunctionOfFamilySet) (I:Ensemble U) (X:Ensemble (Ensemble U)) :=
    Xn=GraphOfFamilySets F I X /\ forall (i:U), i ∈ I -> exists Xi:Ensemble U, (|{|i|}, Xi|) ∈ Xn.

  Inductive IndexedSet (Xn:Ensemble (Ensemble (Ensemble (Ensemble U)))) (i:U) : Ensemble U :=
  | Definition_of_IndexedSet: forall (x:U) (Xi:Ensemble U), (|{|i|}, Xi|) ∈ Xn /\ x ∈ Xi -> x ∈ IndexedSet Xn i.

  Inductive FamilyOfSets (Xn:Ensemble (Ensemble (Ensemble (Ensemble U)))) : Ensemble (Ensemble U) :=
  | Definition_of_FamilySets: forall (Xi:Ensemble U), (exists i:U, (|{|i|}, Xi|) ∈ Xn) -> Xi ∈  FamilyOfSets Xn.

  Inductive UnionOfIndexedSets (P:U -> Prop) (X:U -> Ensemble U) : Ensemble U :=
  | Definition_of_UnionOfIndexedSets: forall(x:U), (exists i:U, P i /\ x ∈ (X i)) -> x ∈ UnionOfIndexedSets P X.

  Inductive IntersectionOfIndexedSets (P:U -> Prop) (X:U -> Ensemble U) : Ensemble U :=
  | Definition_of_IntersectionOfIndexedSets:  forall(x:U), (forall i:U, P i /\ x ∈ (X i)) -> x ∈ IntersectionOfIndexedSets P X.

  Goal forall (i:U)
              (Xn:Ensemble (Ensemble (Ensemble (Ensemble U))))
              (XX:Ensemble (Ensemble U)),
      i ∈ I -> MappingFamilyOfSets Xn FunctionOfFamilySetUpCast I XX <-> Xn ≔ IndexedFunction ⊦ (SetOfSingleton I) ⟼ XX.
  Proof.
    move => i Xn XX HiI.
    rewrite /iff.
    split => H.
    inversion H as [Hf HfS].
    split.
    apply /Extensionality_Ensembles.
    split => Z HZ.
    rewrite Hf in HZ.
    inversion HZ.
    inversion H0.
    split.
    split.
    rewrite H2.
    reflexivity.
    done.
    inversion HZ as [Ii Xi].
    rewrite Hf.
    inversion H0.
    apply ordered_pair_in_direct_product_iff_and in H3.
    inversion H3.
    inversion H4 as [i0].
    split.
    split.
    rewrite H2.
    rewrite -H7.
    reflexivity.
    apply ordered_pair_in_direct_product_iff_and.
    rewrite H7.
    apply H3.
    move => I0 HI0inII.
    inversion HI0inII as [i0].
    apply HfS.
    apply H0.
    split.
    inversion H.
    apply /Extensionality_Ensembles.
    split => Z HZ.
    rewrite H0 in HZ.
    inversion HZ as [I0 Xi].
    inversion H2.
    apply ordered_pair_in_direct_product_iff_and in H5.
    inversion H5.
    inversion H6 as [i0].
    split.
    split.
    rewrite H4.
    rewrite -H9.
    reflexivity.
    apply ordered_pair_in_direct_product_iff_and.
    rewrite H9.
    apply H5.
    inversion HZ.
    rewrite H0.
    inversion H2.
    split.
    split.
    rewrite H4.
    reflexivity.
    done.
    move => i0 Hi0inI.
    inversion H as [Hf HfS].
    apply HfS.
    split.
    apply Hi0inI.
  Qed.

  Goal forall (i:U)
              (Xn:Ensemble (Ensemble (Ensemble (Ensemble U))))
              (XX:Ensemble (Ensemble U)),
      i ∈ I /\ MappingFamilyOfSets Xn FunctionOfFamilySetUpCast I XX -> IndexedSet Xn i ∈ XX.
  Proof.
    move => i Xn XX [H [Hf HfS]].
    have L1: exists Xi:Ensemble U, ((|{|i|}, Xi|)) ∈ Xn.
    apply HfS.
    done.
    inversion L1 as [Xi].
    have L2: Xi = IndexedSet Xn i.
    apply /Extensionality_Ensembles.
    split => x H'.
    suff: ((|{|i|}, Xi|)) ∈ Xn /\ x ∈ Xi.
    apply Definition_of_IndexedSet.
    done.
    inversion H' as [x' Xi' []].
    rewrite Hf in H0.
    inversion H0.
    apply ordered_pair_iff in H4.
    inversion H4.
    inversion H5.
    inversion Hf in H1.
    inversion H1.
    apply ordered_pair_iff in H11.
    inversion H11.
    inversion H12.
    rewrite -H7.
    rewrite H8.
    apply (eq_singleton_eq_element_iff i0 i) in H6.
    apply (eq_singleton_eq_element_iff i1 i) in H13.
    rewrite H6 -H13 -H15 H14.
    done.
    rewrite -L2.
    rewrite Hf in H0.
    inversion H0 as [x' Xi' []].
    apply ordered_pair_iff in H3.
    inversion H3.
    apply ordered_pair_in_direct_product_iff_and in H2.
    inversion H2.
    rewrite H5 in H7.
    done.
  Qed.

  Goal forall (i:U)
              (Xn:Ensemble (Ensemble (Ensemble (Ensemble U))))
              (XX:Ensemble (Ensemble U)),
      i ∈ I /\ MappingFamilyOfSets Xn FunctionOfFamilySetUpCast I XX -> IndexedSet Xn i ∈ FamilyOfSets Xn.
  Proof.
    move => i Xn XX [H [Hf HfS]].
    have L1: exists Xi:Ensemble U, ((|{|i|}, Xi|)) ∈ Xn.
    apply HfS.
    done.
    inversion L1 as [Xi].
    have L2: Xi = IndexedSet Xn i.
    apply /Extensionality_Ensembles.
    split => x H'.
    suff: ((|{|i|}, Xi|)) ∈ Xn /\ x ∈ Xi.
    apply Definition_of_IndexedSet.
    done.
    inversion H' as [x' Xi' []].
    rewrite Hf in H0.
    inversion H0.
    apply ordered_pair_iff in H4.
    inversion H4.
    inversion H5.
    inversion Hf in H1.
    inversion H1.
    apply ordered_pair_iff in H11.
    inversion H11.
    inversion H12.
    rewrite -H7.
    rewrite H8.
    apply (eq_singleton_eq_element_iff i0 i) in H6.
    apply (eq_singleton_eq_element_iff i1 i) in H13.
    rewrite H6 -H13 -H15 H14.
    done.
    rewrite -L2.
    split.
    exists i.
    apply H0.
  Qed.

End FamilyOfSetsPrototype.
