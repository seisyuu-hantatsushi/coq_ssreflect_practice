From mathcomp Require Import ssreflect.

Require Import set_notations.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*
   直観主義論理では
      "a=0\/b=0 -> a*b=0"は証明できるが,
      "a*b=0 -> a=0 \/ b=0は証明できない.
*)

(* Reference 1 [R1]:集合と位相 斎藤毅      ISBN 978-4-13-062958-4 *)
(* Reference 2 [R2]:数学の基礎 島内剛一                           *)
Section PairExamples.
  Variable U:Type.

  Import SetNotations.

  Goal forall (a b:U), a<>b -> {|a|} <> {|b|}.
  Proof.
    move => a b HF.
    rewrite /not.
    move => H.
    apply HF.
    apply Singleton_inv.
    rewrite H.
    apply Singleton_intro.
    reflexivity.
  Qed.

  Goal forall (A B C:Ensemble U), (A ∪ B) = (B ∩ C) -> A ⊂ B /\ B ⊂ C.
  Proof.
    move => A B C.
    split => x.
    move => H1.
    have L1: x ∈ (A ∪ B).
    left.
    apply H1.
    rewrite H in L1.
    inversion L1.
    apply H0.
    move => H1.
    have L1: x ∈ (A ∪ B).
    right.
    apply H1.
    rewrite H in L1.
    inversion L1.
    apply H2.
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

  Theorem T_1: forall (V:Type) (a b c d: V), a <> c -> {|a,b|}={|c,d|} -> a = d.
  Proof.
    +move => V a b c d H0 H1.
     --have L1: a ∈ {|a,b|}.
       left.
       apply Singleton_intro.
       reflexivity.
    +rewrite H1 in L1.
    +move: L1.
     rewrite theorem_of_pairing.
     rewrite -imp_not_l.
     case.
     apply.
     apply H0.
     apply classic.
  Qed.

  Theorem T_2: forall (V:Type) (a b c d: V),
      {|a,b|}={|c,d|} <-> (a = c /\ b = d) \/ (a = d /\ b = c).
  Proof.
    +move => V.
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
    +move => a b c d.
     rewrite /iff.
     split.
     ++move => H.
       apply imp_not_l.
       apply classic.
     --have L1: a <> c \/ b <> d <-> (a = c /\ b = d -> False).
       rewrite /iff.
       split => H0.
       apply or_not_and.
       apply H0.
       apply not_and_or.
       rewrite /not.
       apply H0.
    ++rewrite -L1.
      case => H0.
      split.
      +++move: H.
         move: H0.
         apply T_1. (* a <> c -> a = d *)
      ---have L20: c ∈ {|a,b|}.
         rewrite H.
         left.
         apply Singleton_intro.
         reflexivity.
      ---have L21: c = a \/ c = b.
         move: L20.
         apply theorem_of_pairing.
    ++move: H0. (* a = c \/ b = c ->  a <> c -> b = c *)
      move: L21.
      rewrite (eq_iff c a).
      rewrite (eq_iff c b).
      apply L0.
    +split.
     ---have L30: d ∈ {|a, b|}.
        rewrite H.
        right.
        apply Singleton_intro.
        reflexivity.
     ---have L31: d = a \/ d = b.
        move: L30.
        apply theorem_of_pairing.
     ++move: H0.
       move: L31.
       rewrite (eq_iff d a).
       rewrite (eq_iff d b).
       rewrite or_comm.
       apply L0.
       move: H0.
       apply imp_not_l.
       apply classic.
       apply theorem_of_pairing.
       ---have L10: {|d,c|} = {|c,d|}.
          apply /Extensionality_Ensembles.
          split => x; case => y; move => H2.
          right.
          apply H2.
          left.
          apply H2.
          right.
          apply H2.
          left.
          apply H2.
     ++rewrite L10.
       rewrite -H.
       right.
       apply Singleton_intro.
       reflexivity.
    +case; case => [H0 H1]; rewrite H0; rewrite H1.
     ++reflexivity.
       ---have L1: {|d,c|} = {|c,d|}.
          apply /Extensionality_Ensembles.
          split => x; case => y; move => H2.
          right.
          apply H2.
          left.
          apply H2.
          right.
          apply H2.
          left.
          apply H2.
     ++apply L1.
  Qed.

  Theorem ordered_pair_iff: forall (w x y z: U), (| x , y |) = (| w , z |) <-> x = w /\ y = z.
  Proof.
     unfold OrderedPair.
    +move => w x y z.
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

  Goal forall (x y z : U), x <> y -> ~({|x,z|}={|y|}).
  Proof.
    move => x y z H.
    apply not_eq_sym.
    rewrite /not.
    move => H1.
    apply H.
    apply eq_sym.
    apply Singleton_inv.
    rewrite H1.
    left.
    apply Singleton_intro.
    reflexivity.
  Qed.

  Theorem DirectProduct_Product_Empty: forall (X:Ensemble U), X × {||} = {||}.
  Proof.
    move => X.
    apply /Extensionality_Ensembles.
    split => Y.
    -case.
     move => Z.
     case => x.
     case => y.
     case => [H1 [H2 H3]].
     rewrite H3.
     apply NNPP.
     rewrite /not => H4.
     move: H2.
     apply Noone_in_empty.
    -move => H0.
     apply NNPP.
     rewrite /not => H1.
     move: H0.
     apply Noone_in_empty.
  Qed.

  Theorem DirectProduct_Product_Empty_Comm: forall (X:Ensemble U), X × {||} = {||} × X.
  Proof.
    move => X.
    apply /Extensionality_Ensembles.
    split => Y; rewrite DirectProduct_Product_Empty.
    -move => H0.
     apply NNPP.
     rewrite /not => H1.
     move : H0.
     apply Noone_in_empty.
    -case => Z.
     case => x.
     case => y.
     case => [H0 [H1 H2]].
     apply NNPP.
     rewrite /not => H3.
     move: H0.
     apply Noone_in_empty.
  Qed.

  (* R1 定義 1.3.1 *)
  (* R2 P.82-83 直積 *)
  Goal forall (x y:U) (A B:Ensemble U), (x ∈ A /\ y ∈ B) -> OrderedPair x y ∈ 𝔓(𝔓(A ∪ B)).
  Proof.
    move => x y A B.
    case => [HA HB].
    rewrite /OrderedPair.
    split.
    move => X.
    move => H1.
    split.
    move => z.
    inversion H1.
    inversion H.
    case.
    left.
    apply HA.
    inversion H1.
    inversion H.
    case; move => w.
    case.
    left.
    apply HA.
    case.
    right.
    apply HB.
    inversion H2.
    case; move => w.
    case.
    left.
    apply HA.
    case.
    right.
    apply HB.
  Qed.

  Goal forall (X Y A B: Ensemble U), A ⊂ X /\ B ⊂ Y -> (A × B) ⊂ (X × Y).
  Proof.
    move => X Y A B.
    case => [HAX HBY Z].
    move => H.
    inversion H.
    inversion H0.
    inversion H2.
    inversion H3.
    inversion H5.
    rewrite H7.
    split.
    exists x.
    exists x0.
    split.
    move: H4.
    apply HAX.
    split.
    move: H6.
    apply HBY.
    reflexivity.
  Qed.

  Theorem DirectProductLeftDistUnion :
    forall (A B C: Ensemble U), A × (B ∪ C) = A × B ∪ A × C.
  Proof.
    move => A B C.
    apply /Extensionality_Ensembles.
    split => X.
    -case => Z.
     case => x.
     case => y.
     case => [HA [HBC H0]].
     inversion HBC.
    --left.
      split.
      exists x.
      exists y.
      split.
      apply HA.
      split.
      apply H.
      apply H0.
    --right.
      split.
      exists x.
      exists y.
      split.
      apply HA.
      split.
      apply H.
      apply H0.
    -case => Y.
     --case => Z.
       case => x.
       case => y.
       case => [HA [HB HZ]].
       split.
       exists x.
       exists y.
       split.
       apply HA.
       split.
       left.
       apply HB.
       apply HZ.
     --case => Z.
       case => x.
       case => y.
       case => [HA [HC HZ]].
       split.
       exists x.
       exists y.
       split.
       apply HA.
       split.
       right.
       apply HC.
       apply HZ.
  Qed.

  Theorem DirectProductLeftDistIntersection :
    forall (A B C: Ensemble U), A × (B ∩ C) = A × B ∩ A × C.
  Proof.
    move => A B C.
    apply /Extensionality_Ensembles.
    split => X; case => Z.
    case => x.
    case => y.
    case => [HA [HBC H0]].
     inversion HBC.
     split; split; exists x; exists y; split.
     --apply HA.
       split.
       apply H.
       apply H0.
     --apply HA.
       split.
       apply H1.
       apply H0.
    -move => H0.
     move => H1.
     inversion H0 as [D H01].
     inversion H01 as [x0 H02].
     inversion H02 as [y0 H03].
     inversion H03 as [HA0 H04].
     inversion H04 as [HB0 H05].
     inversion H1 as [E H11].
     inversion H11 as [x1 H12].
     inversion H12 as [y1 H13].
     inversion H13 as [HA1 H14].
     inversion H14 as [HB1 H15].
     have L1: x0 = x1 /\ y0 = y1.
     move: H15.
     rewrite H05.
     apply ordered_pair_iff.
     split.
     exists x1.
     exists y1.
     split.
     apply HA1.
     split.
     move: L1.
     case.
     move => H16 H17.
     split.
     rewrite -H17.
     apply HB0.
     apply HB1.
     apply H15.
  Qed.

  (*
    { A ∈ P(X ∪ Y) | {a} ⊂ A ⊂ {a, b} }
    -> { A | A ∈ P(X ∪ Y) /\ {a} ⊂ A /\ A ⊂ {a, b} }
  *)
  Goal forall (a b:U) (X Y A:Ensemble U), a ∈ X /\ b ∈ Y -> (| a, b |) ⊂ {| A | fun A => A ∈ 𝔓(X ∪ Y) /\ {|a|} ⊂ A /\ A ⊂ {|a, b|} |}.
  Proof.
    move => a b X Y A.
    case => [Ha Hb Z].
    -case => W.
     --case.
       split.
       split.
       split => x.
       case.
       left.
       exact.
     --split.
       exact.
     --left.
       exact.
    -case.
     split.
     --split.
       split => x.
       case => y; case.
       ---left.
          exact.
       ---right.
          exact.
     --split => x.
       left.
       exact.
       exact.
  Qed.

  Goal forall (a b: U) (X Y A:Ensemble U), a ∈ X /\ b ∈ Y -> {| A | fun A => A ∈ 𝔓(X ∪ Y) /\ {|a|} ⊂ A /\ A ⊂ {|a, b|} |} ⊂ (| a, b |).
  Proof.
    move => a b X Y A.
    case => HaX HbY Z.
    case => W.
    case => HP.
    case => Ha Hab.
    move: HP.
    case.
    move => S.
    rewrite /OrderedPair.
    move => HS.
    left.
    rewrite /Included in HS.
    move: (HS a) => HSa.
    rewrite /Included in Ha.
    rewrite /In.
    have L1: S = {|a|}.
    apply /Extensionality_Ensembles.
    split => x.
  Abort.

  (* R1 A 1.3.4 2 *)
  Goal forall (a b x:U) (X Y:Ensemble U), (a ∈ X /\ b ∈ Y /\ x ∈ X) -> ( x = a <-> forall (z:Ensemble U), (z ∈ (| a, b |)) -> x ∈ z ).
  Proof.
    move => a b x X Y.
    case => [HaX [HbY HxX]].
    rewrite /iff.
    split.
    -move => Hax z.
     rewrite Hax.
     case => y.
     case.
     reflexivity.
     case.
     left.
     reflexivity.
    -move => H1.
     apply eq_sym.
     apply Singleton_inv.
     apply (H1 {|a|}).
     left.
     split.
  Qed.

  Lemma L1: forall (X Y:Ensemble U), ((X = {||}) \/ (Y = {||}) -> False) <-> ((X = {||}) -> False) /\ ((Y = {||}) -> False).
  Proof.
    move => X Y.
    rewrite /iff.
    split.
    apply not_or_and.
    case.
    move => HX HY.
    case.
    apply HX.
    apply HY.
  Qed.

  (*
      古典論理では, ¬∀x(x∉A) <-> ∃x(x∈A)
      直観主義論理では, ¬∀x(x∉A)がinhabited,  ∃x(x∈A)がnot emptyで区別される.
   *)
  Lemma L2: forall (X: Ensemble U), (exists x, x ∈ X) -> (X = {||} -> False).
  Proof.
    move => X.
    move => H0 H1.
    move : H0.
    case.
    move => x.
    rewrite H1.
    apply Noone_in_empty.
  Qed.

  Lemma L3: forall (X: Ensemble U), Inhabited U X <-> (X = {||} -> False).
  Proof.
    move => X.
    rewrite /iff.
    split => H0.
    -apply Inhabited_not_empty.
     apply H0.
    -apply not_empty_Inhabited.
     rewrite /not.
     apply H0.
  Qed.

End PairExamples.
