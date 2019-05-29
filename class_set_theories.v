From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import class_set.

Section Class_Set_Theories.

  Variable U:Type.

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

End Class_Set_Theories.