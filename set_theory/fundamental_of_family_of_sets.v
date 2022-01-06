From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import family_of_sets.

Section FundamentalOfFamilySet.

  Variable U:Type.
  Variables X Y I:Ensemble U.
  (* F:U -> Ensemble U となるような写像を作る *)
  Definition FunctionOfFamilySet := U -> Ensemble U.

  Variable IndexedFunction : Ensemble U -> Ensemble U.
  Definition FunctionOfFamilySetUpCast (i:U) := IndexedFunction {|i|}.

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

End FundamentalOfFamilySet.
