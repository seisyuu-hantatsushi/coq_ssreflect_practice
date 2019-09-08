From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import function.

Inductive SetOfSingleton {U:Type} (M:Ensemble U) : Ensemble (Ensemble U) :=
| Definition_of_SetOfSingleton: forall (a:U), a ∈ M -> {|a|} ∈ SetOfSingleton M.

(* FunctionOfFamilySet is type of functional formula *)
Definition FunctionOfFamilySet {U:Type} := U -> Ensemble U.

Inductive GraphOfFamilySets {U:Type} (F:FunctionOfFamilySet) (I:Ensemble U) (XX:Ensemble (Ensemble U)):
  Ensemble (Ensemble (Ensemble (Ensemble U))) :=
| Definition_of_GraphOfFamilySet: forall (i:U) (Xi:Ensemble U), Xi = F i /\ (|{|i|}, Xi|) ∈ (SetOfSingleton I) × XX -> (|{|i|}, Xi|) ∈ GraphOfFamilySets F I XX.

Definition MappingFamilyOfSets {U:Type} (Xn:Ensemble (Ensemble (Ensemble (Ensemble U)))) (F:FunctionOfFamilySet) (I:Ensemble U) (X:Ensemble (Ensemble U)) :=
    Xn=GraphOfFamilySets F I X /\ forall (i:U), i ∈ I -> exists Xi:Ensemble U, (|{|i|}, Xi|) ∈ Xn.

Inductive GraphOfFamilySubsets {U:Type} (F:FunctionOfFamilySet) (I:Ensemble U) (X:Ensemble U):
  Ensemble (Ensemble (Ensemble (Ensemble U))) :=
| Definition_of_GraphOfFamilySubset: forall (i:U) (Xi:Ensemble U), Xi = F i /\ (|{|i|}, Xi|) ∈ (SetOfSingleton I) × (𝔓( X )) -> (|{|i|}, Xi|) ∈ GraphOfFamilySubsets F I X.

Definition MappingFamilyOfSubsets {U:Type} (Xn:Ensemble (Ensemble (Ensemble (Ensemble U)))) (F:FunctionOfFamilySet) (I:Ensemble U) (X:Ensemble U) :=
    Xn=GraphOfFamilySubsets F I X /\ forall (i:U), i ∈ I -> exists Xi:Ensemble U, (|{|i|}, Xi|) ∈ Xn.

Inductive IndexedSet {U:Type} (Xn:Ensemble (Ensemble (Ensemble (Ensemble U)))) (i:U) : Ensemble U :=
| Definition_of_IndexedSet: forall (x:U) (Xi:Ensemble U), (|{|i|}, Xi|) ∈ Xn /\ x ∈ Xi -> x ∈ IndexedSet Xn i.

Inductive FamilyOfSets {U:Type} (Xn:Ensemble (Ensemble (Ensemble (Ensemble U)))) : Ensemble (Ensemble U) :=
| Definition_of_FamilySets: forall (Xi:Ensemble U), (exists i:U, (|{|i|}, Xi|) ∈ Xn) -> Xi ∈  FamilyOfSets Xn.

Inductive UnionOfIndexedSets {U:Type} (P:U -> Prop) (X:U -> Ensemble U) : Ensemble U :=
| Definition_of_UnionOfIndexedSets: forall(x:U), (exists i:U, P i /\ x ∈ (X i)) -> x ∈ UnionOfIndexedSets P X.

Inductive IntersectionOfIndexedSets {U:Type} (P:U -> Prop) (X:U -> Ensemble U) : Ensemble U :=
| Definition_of_IntersectionOfIndexedSets:  forall(x:U), (forall i:U, P i /\ x ∈ (X i)) -> x ∈ IntersectionOfIndexedSets P X.

(* ⋃ : Unicode 22C3 (N-ARY UNION) *)
Notation "⋃ [ P ] X " := (UnionOfIndexedSets P X) (at level 45).
(* ⋂ : Unicode 22C2 (N-ARY INTERSECTION) *)
Notation "⋂ [ P ] X " := (IntersectionOfIndexedSets P X) (at level 45).

Section FamilyOfSets.
  Variable U:Type.
  Variable I X Y:Ensemble U.

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

  Variable IndexedFunction : U -> Ensemble U.

  Theorem union_of_family_of_sets:
    forall (Xn:Ensemble (Ensemble (Ensemble (Ensemble U))))
           (XX:Ensemble (Ensemble U))
           (Xu:U -> Ensemble U)
           (I0 I1: Ensemble U),
      MappingFamilyOfSets Xn IndexedFunction I XX /\ Xu = (IndexedSet Xn) /\ I = I0 ∪ I1 ->
      ⋃ [ fun (i:U) => i ∈ I ] Xu = ⋃ [fun (i:U) => i ∈ I0] Xu ∪ ⋃ [ fun (i:U) => i ∈ I1] Xu.
  Proof.
    move => Xn XX Xu I0 I1 [[Hf HfS] [HX H]].
    rewrite HX.
    apply /Extensionality_Ensembles.
    split => x H'.
    inversion H' as [x0 [i []]].
    inversion H1 as [x1 Xi []].
    rewrite H in H0.
    inversion H0 as [i0 H6|i0 H6]; [left|right]; split; exists i; split.
    apply H6.
    done.
    apply H6.
    done.
    rewrite H.
    inversion H'; split; inversion H0; inversion H2 as [i' []]; exists i'; split.
    left.
    done.
    done.
    right.
    done.
    done.
  Qed.

  Theorem intersection_of_family_of_sets:
    forall (Xn:Ensemble (Ensemble (Ensemble (Ensemble U))))
           (XX:Ensemble (Ensemble U))
           (Xu:U -> Ensemble U)
           (I0 I1: Ensemble U),
      MappingFamilyOfSets Xn IndexedFunction I XX /\ Xu = (IndexedSet Xn) /\ I = I0 ∩ I1 ->
      ⋂ [fun (i:U) => i ∈ I] Xu = ⋂ [fun (i:U) => i ∈ I0] Xu ∩ ⋂ [fun (i:U) => i ∈ I1] Xu.
  Proof.
    move => Xn XX Xu I0 I1 [[Hf HfS] [HX H]].
    rewrite HX.
    apply /Extensionality_Ensembles.
    split => x H'.
    rewrite H in H'.
    inversion H' as [x0].
    split; split => i; move: (H0 i) => H0i; inversion H0i; split; inversion H2; done.
    inversion H'.
    inversion H0.
    inversion H1.
    rewrite H.
    split => i.
    move: (H3 i) (H5 i) => H3i H5i.
    inversion H3i.
    inversion H5i.
    split.
    split.
    apply H7.
    apply H9.
    apply H8.
  Qed.

  Proposition indexed_set_is_element_of_codomain: forall (i:U)
                       (Xn:Ensemble (Ensemble (Ensemble (Ensemble U))))
                       (XX:Ensemble (Ensemble U)),
      i ∈ I /\ MappingFamilyOfSets Xn IndexedFunction I XX -> IndexedSet Xn i ∈ XX.
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

  Proposition indexed_set_is_element_of_family_of_set:
    forall (i:U)
           (Xn:Ensemble (Ensemble (Ensemble (Ensemble U))))
           (XX:Ensemble (Ensemble U)),
      i ∈ I /\ MappingFamilyOfSets Xn IndexedFunction I XX -> IndexedSet Xn i ∈ FamilyOfSets Xn.
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

  Theorem union_of_family_of_subsets:
    forall (Xn:Ensemble (Ensemble (Ensemble (Ensemble U))))
           (Xu:U -> Ensemble U)
           (I0 I1: Ensemble U),
      MappingFamilyOfSubsets Xn IndexedFunction I X /\ Xu = (IndexedSet Xn) /\ I = I0 ∪ I1 ->
      ⋃ [ fun (i:U) => i ∈ I ] Xu = ⋃ [fun (i:U) => i ∈ I0] Xu ∪ ⋃ [ fun (i:U) => i ∈ I1] Xu.
  Proof.
    move => Xn Xu I0 I1 [[Hf HfS] [HX H]].
    rewrite HX.
    apply /Extensionality_Ensembles.
    rewrite Hf H.
    split => x H'.
    inversion H' as [x' [i' []]].
    inversion H0 as [i0 | i0]; [left|right]; split; exists i'; split; done.
    inversion H' as [x' | x']; inversion H0 as [x0 [i0 []]]; inversion H3; inversion H5; inversion H7; inversion H10; apply ordered_pair_in_direct_product_iff_and in H12; inversion H12; apply set_of_singleton_cast in H13; apply ordered_pair_iff in H9;inversion H9; apply (eq_singleton_eq_element_iff i i0) in H15; split; exists i; split.
    apply H13.
    rewrite -H15 in H3.
    done.
    apply H13.
    rewrite -H15 in H3.
    done.
  Qed.

  Theorem intersection_of_family_of_subsets:
    forall (Xn:Ensemble (Ensemble (Ensemble (Ensemble U))))
           (Xu:U -> Ensemble U)
           (I0 I1: Ensemble U),
      MappingFamilyOfSubsets Xn IndexedFunction I X /\ Xu = (IndexedSet Xn) /\ I = I0 ∩ I1 ->
      ⋂ [fun (i:U) => i ∈ I] Xu = ⋂ [fun (i:U) => i ∈ I0] Xu ∩ ⋂ [fun (i:U) => i ∈ I1] Xu.
  Proof.
    move => Xn Xu I0 I1 [[Hf HfS] [HX H]].
    rewrite HX.
    apply /Extensionality_Ensembles.
    rewrite Hf H.
    split => x H'.
    inversion H' as [x'].
    split; split => i; move: (H0 i) => H0i; inversion H0i;inversion H2; split; done.
    split => i.
    inversion H'.
    inversion H0.
    inversion H1.
    move: (H3 i) => H3i.
    move: (H5 i) => H5i.
    inversion H3i.
    inversion H5i.
    split.
    split; done.
    done.
  Qed.

  Proposition indexed_subset_is_element_of_codomain:
    forall (i:U)
           (Xn:Ensemble (Ensemble (Ensemble (Ensemble U)))),
      i ∈ I /\ MappingFamilyOfSubsets Xn IndexedFunction I X -> IndexedSet Xn i ∈ 𝔓( X ).
  Proof.
    move => i Xn [Hi [Hf HfS]].
    split => x H.
    rewrite Hf in H.
    inversion H.
    inversion H0.
    inversion H2 as [i0 Xi' []].
    apply ordered_pair_in_direct_product_iff_and in H5.
    inversion H5.
    inversion H8.
    apply H9.
    apply ordered_pair_iff in H6.
    inversion H6.
    rewrite H12.
    done.
  Qed.

  Proposition indexed_subset_is_element_of_family_of_set:
    forall (i:U)
           (Xn:Ensemble (Ensemble (Ensemble (Ensemble U)))),
      i ∈ I /\ MappingFamilyOfSubsets Xn IndexedFunction I X -> IndexedSet Xn i ∈ FamilyOfSets Xn.
  Proof.
    move => i Xn [H [Hf HfS]].
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
    rewrite -H7 H8.
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
    inversion H7.
    split.
    exists i.
    rewrite Hf.
    done.
  Qed.

End FamilyOfSets.

Require Export function.