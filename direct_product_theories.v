From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import logic_theories.
Require Import class_set_theories.

Section Direct_Product_Theories.

  Variable U:Type.

  Theorem direct_product_empty_r: forall (X:Ensemble U), X × {||} = {||}.
  Proof.
    move => X.
    apply /Extensionality_Ensembles.
    split => Y.
    -case.
     move => Z.
     case => [x [y]].
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

  Theorem direct_product_empty_l: forall (X:Ensemble U), {||} × X = {||}.
  Proof.
    move => X.
    apply /Extensionality_Ensembles.
    split => Y.
    move => H0.
    apply NNPP.
    rewrite /not => H1.
    move: H0.
    case => Z.
    case => [x [y]].
    case => [H2 [H3 H4]].
    move : H2.
    apply Noone_in_empty.
    move => H0.
    apply NNPP.
    rewrite /not => H1.
    move: H0.
    apply Noone_in_empty.
  Qed.

  Theorem direct_product_empty_comm: forall (X:Ensemble U), {||} × X =  X × {||}.
  Proof.
    move => X.
    rewrite direct_product_empty_r.
    rewrite direct_product_empty_l.
    reflexivity.
  Qed.

  Theorem direct_product_empty_iff:
    forall (X Y:Ensemble U), X × Y = {||} <-> X = {||} \/ Y = {||}.
  Proof.
    move => X Y.
    rewrite /iff.
    split.
    apply contrapositive.
    apply classic.
    move => H.
    have L0: ~(forall (x y:U), ~((|x,y|) ∈ X × Y)) -> X × Y = {||} -> False.
    move => HL0 HL1.
    apply HL0.
    rewrite HL1.
    move => x y.
    apply Noone_in_empty.
    apply L0.
    have L1: (exists x y:U, (|x,y|) ∈ X × Y) -> ~(forall (x y:U), ~((|x,y|) ∈ X × Y)).
    case => x.
    case => y.
    move => HL10.
    unfold not.
    move => HL11.
    move: HL10.
    apply HL11.
    apply L1.
    have L2: (exists x y:U, x ∈ X /\ y ∈ Y) -> (exists x y:U, (|x,y|) ∈ X × Y).
    case => x.
    case => y.
    case => HX HY.
    exists x.
    exists y.
    rewrite direct_product_and_iff.
    split.
    apply HX.
    apply HY.
    apply L2.
    have L3: (exists x:U, x ∈ X) /\ (exists y:U, y ∈ Y) -> (exists x y:U, x ∈ X /\ y ∈ Y).
    case.
    case => x HX.
    case => y HY.
    exists x.
    exists y.
    split.
    apply HX.
    apply HY.
    apply L3.
    have L4: ((X = {||} -> False) /\ (Y = {||} -> False)).
    apply not_or_and.
    unfold not.
    apply H.
    inversion L4.
    split; apply not_all_not_ex; unfold not.
    rewrite -Axiom_of_EmptySet.
    apply H0.
    rewrite -Axiom_of_EmptySet.
    apply H1.
    case => H.
    rewrite H.
    rewrite direct_product_empty_l.
    reflexivity.
    rewrite H.
    rewrite direct_product_empty_r.
    reflexivity.
  Qed.

End Direct_Product_Theories.