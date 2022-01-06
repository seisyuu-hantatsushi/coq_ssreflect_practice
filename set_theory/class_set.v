From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Coq.Logic.Decidable. (* Introducing decidable *)
Require Import Coq.Sets.Powerset_Classical_facts.

Notation "x ∈ X" := (In _ X x) (right associativity, at level 48).
Notation "A ⊂ B" := (Included _ A B) (right associativity, at level 51).
Notation "A ⊊ B" := (Strict_Included _ A B) (right associativity, at level 51).
Notation "A ^c"   := (Complement _ A) (at level 47).
Notation "A ∪ B" := (Union _ A B) (left associativity, at level 50).
Notation "A ∩ B" := (Intersection _ A B) (left associativity, at level 50).
Notation "A \ B"  := (Setminus _ A B) (left associativity, at level 50).

Notation "{||}"  := (Empty_set _).
Notation "{| x |}" := (Singleton _ x).
Notation "{| x , y , .. , z |}" := (Union _ .. (Union _ (Singleton _ x) (Singleton _ y)) .. (Singleton _ z)).

Theorem Axiom_of_EmptySet:
  forall (U:Type) (X:Ensemble U), X = {||} <-> (forall (x:U), x ∈ X -> False).
  move => X.
  rewrite /iff.
  split.
  move => HE.
  rewrite HE.
  apply Noone_in_empty.
  move => HF.
  apply /Extensionality_Ensembles.
  split => y.
  move => H0.
  move: (HF y).
  case.
  apply H0.
  case.
Qed.

Theorem not_empty_set_has_element:
  forall (U:Type) (X:Ensemble U), ~(X={||}) <-> exists x:U, x ∈ X.
  Proof.
    rewrite /iff.
    split => H.
    -have L1: Inhabited U X.
     apply not_empty_Inhabited.
     apply H.
     inversion L1.
     exists x.
     apply H0.
    -inversion H as [x].
     apply Inhabited_not_empty.
     apply (Inhabited_intro U X x).
     apply H0.
  Qed.

(* Axiom of separation { x;U | P(x) } *)
Inductive SchemaOfSeparation (U:Type) (x:U) (P:U -> Prop): Ensemble U :=
  Definition_of_Schema_Sepatation:
    forall (x0: U), P x0 -> In U (SchemaOfSeparation x P) x0.

Definition OrderedPair {U:Type} (a b : U) := {|{|a|},{|a,b|}|}.

(* Axiom of the Power Set *)
Inductive DirectProduct {U:Type} (X Y:Ensemble U) : Ensemble (Ensemble (Ensemble U)) :=
  Definition_of_DirectProduct:
    forall (Z: Ensemble (Ensemble U)),
      (exists x:U, exists y:U, (x ∈ X /\ y ∈ Y /\ Z = {|{|x|},{|x,y|}|})) ->
      In (Ensemble (Ensemble U)) (DirectProduct X Y) Z.

(* 𝔓:Unicode 1D513 *)
Notation "𝔓( X )" := (@Power_set _ X) (at level 47).

Notation "X × Y" := (DirectProduct X Y) (at level 47).
Notation "(| a , b |)" := (OrderedPair a b) (at level 48).

(* Binary Relation {z|z=(|x,y|) /\ x ∈ X /\ y ∈ Y} *)

Inductive FirstOfOrderedPair {U:Type} (XY: (Ensemble (Ensemble U))): Ensemble U :=
| ordered_pair_first_accessor: forall (x:U), (exists y:U, (|x,y|) = XY) -> FirstOfOrderedPair XY x.

Inductive SecondOfOrderedPair {U:Type} (XY: (Ensemble (Ensemble U))): Ensemble U :=
| ordered_pair_second_accessor: forall (y:U), (exists x:U, (|x,y|) = XY) -> SecondOfOrderedPair XY y.

Inductive Pr1 {U:Type} (XY: Ensemble (Ensemble (Ensemble U))) : Ensemble U :=
| pr1_accessor: forall (x:U), (exists y:U, (|x,y|) ∈ XY) ->  Pr1 XY x.

Inductive Pr2 {U:Type} (XY: Ensemble (Ensemble (Ensemble U))) : Ensemble U :=
| pr2_accessor: forall (y:U), (exists x:U, (|x,y|) ∈ XY) ->  Pr2 XY y.

Section Class_Set.

  Variable U:Type.

  Lemma eq_iff: forall (V:Type) (x y:V), x = y <-> y = x.
  Proof.
  +move => V x y.
   rewrite /iff.
   split; move => H; rewrite H; reflexivity.
  Qed.

  Lemma singleton_eq_iff: forall (V:Type) (x y: V), x ∈ {|y|} <-> x = y.
  Proof.
    +move => V x y.
     rewrite /iff.
     split => H.
     (* x ∈ {|y|} -> x = y *)
     ++apply eq_sym.
       apply Singleton_inv.
       apply H.
     (* x = y -> x ∈ {|y|} *)
     ++rewrite H.
       apply Singleton_intro.
       reflexivity.
  Qed.

  Lemma eq_singleton_eq_element_iff: forall (x y : U), {|x|} = {|y|} <-> x = y.
  Proof.
    +move => x y.
     rewrite /iff.
     split => H.
     (* {|x|} = {|y|} -> x = y *)
     ++apply Singleton_inv.
       rewrite H.
       apply singleton_eq_iff.
       reflexivity.
     (* x = y -> {|x|} = {|y|} *)
     ++rewrite H.
       reflexivity.
  Qed.

  Theorem theorem_of_pairing: forall (V:Type) (x y z:V), x ∈ {|y,z|} <-> x = y \/ x = z.
  Proof.
    +move => V x y z.
     rewrite /iff.
     split.     (* x ∈ {|y,z|} -> x = y \/ x = z. *)
     ++case => w H.
       left.
       apply singleton_eq_iff.
       apply H.
       right.
       apply singleton_eq_iff.
       apply H.
     (*  x = y \/ x = z -> x ∈ {|y,z|} *)
     ++case => H; rewrite H.
       left.
       reflexivity.
       right.
       reflexivity.
  Qed.

  Theorem T_0: forall (a b c:U), {|a|} = {|b,c|} -> a = b /\ b = c.
  Proof.
    move => a b c H.
    have L1: b ∈ {|b,c|}.
    left.
    apply Singleton_intro.
    reflexivity.
    have L2: a=b.
    rewrite -H in L1.
    apply Singleton_inv.
    apply L1.
    split.
    apply L2.
    rewrite -L2.
    have L3: c ∈ {|b,c|}.
    right.
    apply Singleton_intro.
    reflexivity.
    rewrite -H in L3.
    apply Singleton_inv.
    apply L3.
  Qed.

  Theorem T_1: forall (a b c d: U), a <> c -> {|a,b|}={|c,d|} -> a = d.
  Proof.
    +move => a b c d H0 H1.
     --have L1: a ∈ {|a,b|}.
       left.
       apply Singleton_intro.
       reflexivity.
    +rewrite H1 in L1.
    +move: L1.
     rewrite theorem_of_pairing.
     rewrite -imp_not_l.
     apply.
     apply H0.
     apply classic.
  Qed.

  Theorem T_2: forall (V:Type) (a b c d: V),
      {|a,b|}={|c,d|} <-> (a = c /\ b = d) \/ (a = d /\ b = c).
  Proof.
    move => V.
    (* x = z \/ y = z -> x <> z -> y = z *)
    ++have L0: forall (x y z: V), x = z \/ y = z -> x <> z -> y = z.
      move => x y z H.
      apply or_not_l_iff_2.
      apply classic.
      move: H.
      case => H.
      left.
      case.
      exact H.
      right.
      exact H.
    ++have L1: forall (x y: V), {|x, y|} = {|y, x|}.
      move => x y.
      apply /Extensionality_Ensembles.
      split => z; case => w H.
      right.
      apply H.
      left.
      apply H.
      right.
      apply H.
      left.
      apply H.
    +move => a b c d.
     rewrite /iff.
     split.
     ++move => H.
       apply imp_not_l.
       apply classic.
     --have L2: a <> c \/ b <> d <-> (a = c /\ b = d -> False).
       rewrite /iff.
       split => H0.
       apply or_not_and.
       apply H0.
       apply not_and_or.
       rewrite /not.
       apply H0.
    ++rewrite -L2.
      case => H0.
      split.
      (* a = c \/ a = d -> a <> c -> a = d *)
      ---have L01: a = c \/ a = d.
         apply theorem_of_pairing.
         rewrite -H.
         left.
         apply Singleton_intro.
         reflexivity.
      ---move: H0.
         move: L01.
         rewrite (eq_iff a c).
         rewrite (eq_iff a d).
         apply L0.
      (* a = c \/ b = c -> a <> c -> b = c *)
      ---have L02: a = c \/ b = c.
         rewrite (eq_iff a c).
         rewrite (eq_iff b c).
         apply theorem_of_pairing.
         rewrite H.
         left.
         apply Singleton_intro.
         reflexivity.
      ---move: H0.
         move: L02.
         apply L0.
    +split.
     ++move: H0.
     (* b = d \/ a = d -> b <> d -> a = d *)
       ---have L30: b = d \/ a = d.
          rewrite (eq_iff b d).
          rewrite (eq_iff a d).
          apply theorem_of_pairing.
          rewrite L1.
          rewrite H.
          right.
          apply Singleton_intro.
          reflexivity.
     ++move: L30.
       apply L0.
     (* b = d -> b = c -> b <> d -> b = c *)
     ++move: H0.
       ---have L31: b = d \/ b = c.
          apply theorem_of_pairing.
          rewrite L1.
          rewrite -H.
          right.
          apply Singleton_intro.
          reflexivity.
     ++move: L31.
       rewrite (eq_iff b d).
       rewrite (eq_iff b c).
       apply L0.
    +case; case => [H0 H1]; rewrite H0; rewrite H1.
     ++reflexivity.
     ++apply L1.
  Qed.

  Theorem ordered_pair_iff: forall (x y w z: U), (| x , y |) = (| w , z |) <-> x = w /\ y = z.
  Proof.
     unfold OrderedPair.
    +move => x y w z.
     rewrite /iff.
     split.
     (* {|{|x|}, {|x, y|}|} = {|{|w|}, {|w, z|}|} -> x = w /\ y = z *)
     ++move => H0.
       ---have L1: ({|x|}={|w|}/\{|x,y|}={|w,z|}) \/ ({|x|}={|w,z|}/\{|x,y|}={|w|}).
          (* {|{|x|}, {|x, y|}|} = {|{|w|}, {|w, z|}|} -> ({|x|}={|w|}/\{|x,y|}={|w,z|}) \/ ({|x|}={|w,z|}/\{|x,y|}={|w|}) *)
          apply T_2.
          apply H0.
     ++move: L1.
       (* ({|x|} = {|w|} /\ {|x, y|} = {|w, z|}) \/ ({|x|} = {|w, z|} /\ {|x, y|} = {|w|}) -> x = w /\ y = z *)
       case.
       +++case => H00. (* ({|x|} = {|w|} /\ {|x, y|} = {|w, z|}) -> x = w /\ y = z *)
          rewrite T_2.
          case.
          apply.
          case => H01 H02.
          split.
          move: H00.
          apply eq_singleton_eq_element_iff.
          rewrite -H01.
          rewrite H02.
          apply eq_sym.
          move: H00.
          apply eq_singleton_eq_element_iff.
       +++case => H00 H01. (*({|x|} = {|w, z|} /\ {|x, y|} = {|w|}) -> x = w /\ y = z *)
          ----have L1: x = w /\ w = z.
              move: H00.
              apply T_0.
          ----have L2: w = x /\ x = y.
              move: H01.
          ----have L20: {|x,y|} = {|w|} <-> {|w|} = {|x,y|}.
              rewrite /iff.
              split; move => H20; rewrite H20; reflexivity.
       +++rewrite L20.
          apply T_0.
          inversion L1.
          inversion L2.
          split.
          apply H.
          rewrite -H3.
          rewrite -H1.
          apply H.
     (* x = w /\ y = z -> {|{|x|}, {|x, y|}|} = {|{|w|}, {|w, z|}|} *)
     ++case => H0 H1.
       rewrite H0.
       rewrite H1.
       reflexivity.
  Qed.

  Lemma FirstOfOrderedPairAccess: forall (a b:U), FirstOfOrderedPair ((| a, b |)) = {|a|}.
  Proof.
    move => a b.
    apply /Extensionality_Ensembles.
    split => z.
    case => [x [y]].
    rewrite ordered_pair_iff.
    case => H0 H1.
    apply singleton_eq_iff.
    apply H0.
    move => H.
    split.
    exists b.
    apply ordered_pair_iff.
    split.
    apply singleton_eq_iff.
    apply H.
    reflexivity.
  Qed.

  Lemma SecondOfOrderedPairAccess: forall (a b:U), SecondOfOrderedPair ((| a, b |)) = {|b|}.
  Proof.
    move => a b.
    apply /Extensionality_Ensembles.
    split => z.
    case => [y [x]].
    rewrite ordered_pair_iff.
    case => Hxa Hyb.
    apply singleton_eq_iff.
    apply Hyb.
    move => H.
    split.
    exists a.
    rewrite ordered_pair_iff.
    split.
    reflexivity.
    apply singleton_eq_iff.
    apply H.
  Qed.

End Class_Set.

Export Coq.Sets.Powerset_Classical_facts.
Export Coq.Logic.Decidable.
