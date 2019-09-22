From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import logic_theories.
Require Import logic_pred_theories.
Require Import family_of_sets.

Section FamilyOfSetsTheories.
  Variable U:Type.
  Variable I X Y:Ensemble U.
  Variable XX:Ensemble (Ensemble U).
  Variable IndexedFunction : U -> Ensemble U.

  Theorem union_of_empty_family_is_empty_set:
    forall (Xm:Ensemble (Ensemble (Ensemble (Ensemble U))))
           (Xn:U -> Ensemble U),
      MappingFamilyOfSets Xm IndexedFunction I XX /\ Xn = (IndexedSet Xm) -> ⋃ [ fun (i:U) => i ∈ {||} ] Xn = {||}.
  Proof.
    move => Xn Xu [[Hf HfS] H].
    rewrite H.
    apply /Extensionality_Ensembles.
    split => x H'.
    inversion H' as [x' [i' []]].
    inversion H0.
    inversion H'.
  Qed.

  Theorem intersection_of_empty_family_is_full_set:
    forall (Xm:Ensemble (Ensemble (Ensemble (Ensemble U))))
           (Xn:U -> Ensemble U)
           (i:U),
      I={||} /\ i ∈ I /\ MappingFamilyOfSets Xm IndexedFunction I XX /\ Xn = (IndexedSet Xm) -> ⋂ [ fun (i:U) => i ∈ I ] Xn = Full_set U.
  Proof.
    move => Xm Xn i [HI [Hi [[Hf HfS] H]]].
    apply /Extensionality_Ensembles.
    split => x H'.
    done.
    rewrite HI in Hi.
    split => i'.
    split.
    move: Hi.
    case.
    move: Hi.
    case.
  Qed.

  Theorem intersection_of_empty_family_of_subset_is_full_set:
    forall (Xm:Ensemble (Ensemble (Ensemble (Ensemble U))))
           (Xn:U -> Ensemble U)
           (i:U),
      I={||} /\ i ∈ I /\ MappingFamilyOfSubsets Xm IndexedFunction I X /\ Xn = (IndexedSet Xm) ->  ⋂ [ fun (i:U) => i ∈ I ] Xn = X.
  Proof.
    move => Xm Xn i [HI [Hi [[Hf HfS] H]]].
    apply /Extensionality_Ensembles.
    split => x H'.
    inversion H' as [x0].
    move: (H0 i) => [Hi0 Hi1].
    rewrite H in Hi1.
    inversion Hi1 as [x1 Xi []].
    rewrite Hf in H2.
    inversion H2 as [i' Xi' []].
    rewrite H7 in H6.
    apply ordered_pair_in_direct_product_iff_and in H6.
    inversion H6.
    inversion H9.
    apply H10.
    done.
    rewrite HI in Hi.
    split => i'.
    split.
    move: Hi.
    case.
    move: Hi.
    case.
  Qed.

  Theorem distr_union_of_family_of_sets:
    forall (Xm:Ensemble (Ensemble (Ensemble (Ensemble U))))
           (Xn:U -> Ensemble U),
      MappingFamilyOfSets Xm IndexedFunction I XX /\ Xn = (IndexedSet Xm)
      -> ⋃ [ fun (i:U) => i ∈ I ] Xn ∩ Y = ⋃ [ fun (i:U) => i ∈ I ] (fun i:U => (Xn i) ∩ Y).
  Proof.
    move => Xm Xn [[Hf HfS] H].
    apply /Extensionality_Ensembles.
    split => x H'; inversion H'.
    inversion H0 as [x'].
    split.
    inversion H3 as [i].
    exists i.
    inversion H5.
    split.
    done.
    split; done.
    inversion H0 as [i].
    inversion H2.
    inversion H4.
    split.
    split.
    exists i.
    split; done.
    done.
  Qed.

  Theorem distr_intersection_of_family_of_sets:
    forall (Xm:Ensemble (Ensemble (Ensemble (Ensemble U))))
           (Xn:U -> Ensemble U),
      MappingFamilyOfSets Xm IndexedFunction I XX /\ Xn = (IndexedSet Xm) /\ (forall (i x:U), i ∈ I /\ x ∈ Y)
      -> ⋂ [ fun (i:U) => i ∈ I ] Xn ∪ Y = ⋂ [ fun (i:U) => i ∈ I ] (fun i:U => (Xn i) ∪ Y).
  Proof.
    move => Xm Xn [[Hf HfS] [HXn HixY]].
    apply /Extensionality_Ensembles.
    +split => x.
     move => H.
     inversion H.
     (* x x ∈ ⋂ [fun i : U => i ∈ I] Xn -> x ∈ ⋂ [fun i : U => i ∈ I] (fun i : U => Xn i ∪ Y) *)
     inversion H0.
     split => i.
     move: (H2 i) => [Hi HXi].
     split.
     apply Hi.
     left.
     done.
     (* x x ∈ Y -> x ∈ ⋂ [fun i : U => i ∈ I] (fun i : U => Xn i ∪ Y) *)
     split => i.
     move: (HixY i x) => [Hi HY].
     split.
     apply Hi.
     right.
     done.
    +move => H.
     have L1: (forall i:U, i ∈ I) /\ (forall x:U, x ∈ Y).
     apply forall_bound_variable_and_out_2.
     done.
     inversion L1.
     inversion H.
     have L2: (forall i:U, i ∈ I) /\ (forall (i:U), x ∈ (Xn i ∪ Y)).
     apply forall_bound_variable_and_dist_iff.
     done.
     inversion L2.
     have L3: forall (i:U), x ∈ (Xn i) \/ x ∈ Y.
     move => i.
     move: (H5 i).
     case => x1 H6; [left|right]; done.
     have L4: (forall (i:U), x ∈ (Xn i)) \/ x ∈ Y.
     apply or_comm.
     apply forall_bound_variable_or_out.
     move => i.
     apply or_comm.
     done.
     move: L4.
     case => H'.
     (* (forall i : U, x ∈ Xn i) -> x ∈ (⋂ [fun i : U => i ∈ I] Xn ∪ Y) *)
     left.
     split.
     apply forall_bound_variable_and_dist_iff.
     split.
     apply H4.
     done.
     (* (x ∈ Y) -> x ∈ (⋂ [fun i : U => i ∈ I] Xn ∪ Y) *)
     right.
     apply H'.
  Qed.

End FamilyOfSetsTheories.