From mathcomp Require Import ssreflect.

Require Import Coq.Sets.Powerset_Classical_facts.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module SetsNotations.
  Variable U V: Type.
  Notation "x ∈ X" := (In _ X x) (at level 48).
  Notation "A ⊂ B" := (Included _ A B) (at level 48).
  Notation "A ^c"   := (Complement _ A) (at level 49).
  Notation "A ∪ B" := (Union _ A B) (at level 50).
  Notation "A ∩ B" := (Intersection _ A B) (at level 50).
  Notation "A \ B" := (Setminus _ A B) (at level 50).

  (*
     {a, b, c} = ∃x{x|x=a \/ x=b \/ x=c}
       -> (∀x(x=a \/ x=b \/ x=c) -> x)
   *)

  Variable x y: U.
  Variable a b c: U.
  Definition S0 := Add U (Empty_set U) a.
  Definition S1 := Add U (Add U (Empty_set U) a) b.
  Definition S2 := Add U (Add U (Add U (Empty_set U) a) b) c.
  Definition P_S2 (x:U): Prop
    := (x = a) \/ (x = b) \/ (x = c).
  Notation "{| x | P |}" := P.
  Notation "{||}" := (Empty_set _).
  
  Goal In U S0 a.
  Proof.
    rewrite /In.
    rewrite /S0.
    rewrite /Add.
    right.
    rewrite /In.
    apply In_singleton.
  Qed.

  Goal In U S1 a \/ In U S1 c.
  Proof.
    left.
    rewrite /In.
    rewrite /S1.
    rewrite /Add.
    left.
    right.
    apply In_singleton.
  Qed.

  Goal In U P_S2 a.
  Proof.
    rewrite /In.
    rewrite /P_S2.
    left.
    apply eq_refl.
  Qed.

  Goal forall (A:Ensemble U), A = A ∪ {||}.
  Proof.
    move => A.
    apply: Extensionality_Ensembles.
    rewrite /Same_set.
    split.
    move => x H1.
    left.
    apply H1.
    move => x.
    case.
    done.
    done.
  Qed.

  Goal forall (A:Ensemble U),  {||} = A ∩ {||}.
  Proof.
    move => A.
    apply: Extensionality_Ensembles.
    rewrite /Same_set.
    split.
    +move => x H1.
     split.
     move: H1.
     case.
     apply H1.
    +move => x.
     case.
     move => x0.
     move => H1.
     apply.
  Qed.

  Goal P_S2 = S2.
  Proof.
    apply: Extensionality_Ensembles.
    rewrite /Same_set.
    split => z.
    move => H1.
    inversion H1.
    rewrite H.
    rewrite /In.
    rewrite /S2.
    rewrite /Add.
    left.
    left.
    right.
    apply In_singleton.
    inversion H.
    rewrite H0.
    rewrite /In.
    rewrite /S2.
    rewrite /Add.
    left.
    right.
    apply In_singleton.
    rewrite H0.
    rewrite /In.
    rewrite /S2.
    rewrite /Add.
    right.
    apply In_singleton.
    move => H1.
    rewrite /P_S2.
    inversion H1.
    inversion H.
    inversion H2.
    left.
    move: H4.
    done.
    left.
    apply eq_sym.
    apply Singleton_inv.
    apply H4.
    right.
    left.
    apply eq_sym.
    apply Singleton_inv.
    apply H2.
    right.
    right.
    apply eq_sym.
    apply Singleton_inv.
    apply H.
  Qed.

  Notation "{| x |}" := (fun w => w = x).
  Notation "{| x , y , .. , z |}" := (fun w => (or .. (or (w=x) (w=y)) .. (w=z))).

  Lemma neq_imply_not_in_singletion:
    forall  (U:Type) (a b:U), a <> b -> ~(b ∈ Singleton U a).
  Proof.
    move => U0 a0 b0 Hneq.
    rewrite /not.
    move => H1.
    inversion H1.
    move: Hneq.
    rewrite /not.
    apply.
    apply H.
  Qed.

  Goal {| a, b, c |} = P_S2.
  Proof.
    apply: Extensionality_Ensembles.
    rewrite /Same_set.
    split.
    -rewrite /P_S2.
     rewrite /Included.
     move => w.
     rewrite /In.
     move => H1.
     rewrite -or_assoc.
     apply H1.
    -rewrite /P_S2.
     rewrite /Included.
     move => w.
     rewrite /In.
     move => H1.
     rewrite or_assoc.
     apply H1.
  Qed.

  Goal Empty_set U ⊂ {| a, b, c |}.
  Proof.
    move => w.
    done.
  Qed.

  Goal {| a, b |} = {| b, a |}.
  Proof.
    apply: Extensionality_Ensembles.
    rewrite /Same_set.
    split; move => w; rewrite /In; move => H1; apply or_comm; exact H1.
  Qed.

  Goal {| a |} = Singleton U a.
  Proof.
    apply: Extensionality_Ensembles.
    rewrite /Same_set.
    split; move => w; rewrite /In; move => H1; rewrite -H1; done.
  Qed.

  Goal {| a, a |} = Singleton U a.
  Proof.
    apply: Extensionality_Ensembles.
    rewrite /Same_set.
    split; move => w; rewrite /In.
    case; move => H1; rewrite H1; done.
    case.
    left.
    done.
  Qed.
(*
  Check {|a, b|}.
  Check (a <> b).
*)
  Goal a <> b -> a ∈ (Subtract U S1 b).
  Proof.
    move => H1.
    move: (Subtract_intro U S1 b a).
    apply.
    rewrite /In.
    rewrite /S1.
    rewrite /Add.
    left.
    right.
    done.
    apply not_eq_sym.
    apply H1.
  Qed.

  Goal a <> b -> ~(b ∈ (Subtract U S1 b)).
  Proof.
    rewrite /not.
    move => H1.
    case.
    move => H2.
    case.
    done.
  Qed.

  Goal b <> c /\ c <> a -> ~( c ∈ S1 ).
  Proof.
    case => [H1 H2].
    rewrite /S1.
    rewrite /Add.
    move => H3.
    inversion H3.
    inversion H.
    done.
    move: H4.
    apply neq_imply_not_in_singletion.
    move: H2.
    apply not_eq_sym.
    move: H.
    apply neq_imply_not_in_singletion.
    apply H1.
  Qed.

  Goal b <> c /\ c <> a -> ~( c ∈ {|a, b|} ).
  Proof.
    case => [H1 H2].
    rewrite /not.
    rewrite /In.
    case.
    apply H2.
    move: H1.
    apply not_eq_sym.
  Qed.

End SetsNotations.
