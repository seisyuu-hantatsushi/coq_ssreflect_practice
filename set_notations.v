From mathcomp Require Import ssreflect.

Require Import Coq.Sets.Powerset_Classical_facts.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module SetNotations.
  Notation "x ∈ X" := (In _ X x) (at level 48).
  Notation "A ⊂ B" := (Included _ A B) (at level 48).
  Notation "A ^c"   := (Complement _ A) (at level 49).
  Notation "A ∪ B" := (Union _ A B) (at level 50).
  Notation "A ∩ B" := (Intersection _ A B) (at level 50).
  Notation "A \ B"  := (Setminus _ A B) (at level 50).

  Notation "{||}"  := (Empty_set _).
  Notation "{| x |}" := (Singleton _ x).
  Notation "{| x , y , .. , z |}" := (Union _ .. (Union _ (Singleton _ x) (Singleton _ y)) .. (Singleton _ z)).


  (* { x;U | P(x) } *)
  Inductive SchemaSpecification (U:Type) (x0:U) (P:U -> Prop): Ensemble U :=
    Definition_of_Schema_Spec:
      forall (x: U), P x -> In U (SchemaSpecification x0 P) x.

  Notation "{| x ; U | P |}" := (SchemaSpecification x P).
  Notation "{| x | P |}" := (SchemaSpecification x P).

  Check SchemaSpecification.
End SetNotations.

Export Coq.Sets.Powerset_Classical_facts.

Section Validation.
  Import SetNotations.
  Variable U:Type.
  Variable a b c :U.

  Goal forall (x:U), {| x ; U | (fun x => x = a \/ x = b) |} = {| a, b |}.
  Proof.
    move => x.
    apply: Extensionality_Ensembles.
    split => y.
    case => [z [H1|H1]]; rewrite H1.
    left.
    reflexivity.
    right.
    reflexivity.
    case => z H1; apply Definition_of_Schema_Spec.
    left.
    apply eq_sym.
    apply Singleton_inv.
    apply H1.
    right.
    apply eq_sym.
    apply Singleton_inv.
    apply H1.
  Qed.

  Goal {| a , a |} = {| a |}.
  Proof.
    apply: Extensionality_Ensembles.
    split => x.
    -case; move => y; apply.
    -left.
     apply H.
  Qed.

  Goal {||} ⊂ {| a , b , c |}.
  Proof.
    move => x.
    case.
  Qed.

  Goal {| a, b |} ⊂ {| a , b , c |}.
  Proof.
    move => x.
    case => y H; left.
    -left.
     apply H.
    -right.
     apply H.
  Qed.

  Goal forall (A:Ensemble U), A = A ∪ {||}.
  Proof.
    move => A.
    apply: Extensionality_Ensembles.
    split => x.
    -left.
     apply H.
    -case => y.
     apply.
     case.
  Qed.

  Goal forall (A:Ensemble U), {||} = A ∩ {||}.
  Proof.
    move => A.
    apply: Extensionality_Ensembles.
    split => x.
    -move => H1.
     split.
     move: H1.
     case.
     apply H1.
     case => y H1.
     apply.
  Qed.

  Goal (fun x => x = a \/ x = b \/ x = c) = {| a , b , c |}.
  Proof.
    apply: Extensionality_Ensembles.
    split => x.
    -case => H.
    --left.
      left.
      rewrite H.
      reflexivity.
      inversion H.
    --left.
      right.
      rewrite H0.
      reflexivity.
    --right.
      rewrite H0.
      reflexivity.
    -case => y.
     case => z H1.
     --left.
       apply eq_sym.
       apply Singleton_inv.
       apply H1.
     --right.
       left.
       apply eq_sym.
       apply Singleton_inv.
       apply H1.
     -move => H1.
      right.
      right.
      apply eq_sym.
      apply Singleton_inv.
      apply H1.
  Qed.

End Validation.