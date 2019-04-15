From mathcomp Require Import ssreflect.

Require Import Coq.Sets.Powerset_Classical_facts.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section ProductSet_Example.
  Variable U V: Type.
  Notation "x ∈ X" := (In _ X x) (at level 48).
  Notation "A ⊂ B" := (Included _ A B) (at level 48).
  Notation "A ^c"   := (Complement _ A) (at level 49).
  Notation "A ∪ B" := (Union _ A B) (at level 50).
  Notation "A ∩ B" := (Intersection _ A B) (at level 50).
  Notation "A \ B" := (Setminus _ A B) (at level 50).

  (*
     {a, b, c} = ∃x{x|x=a \/ x=b \/ x=c}
   *)
  
  Variable x y: U.
  Variable a b c: U.
  Definition S := Coq.Sets.Ensembles.Add U (Empty_set U) a.
  Definition S1 := Add U (Add U (Empty_set U) a) b.
  Definition S2 := Add U (Add U (Add U (Empty_set U) a) b) c.
  Definition S_cond (x:U): Prop
    := (x = a) \/ (x = b) \/ (x = c).

  Goal In U S a.
  Proof.
    rewrite /In.
    rewrite /S.
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

  Goal In U S_cond a.
  Proof.
    rewrite /In.
    rewrite /S_cond.
    left.
    apply eq_refl.
  Qed.

  Goal S_cond = S2.
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
    rewrite /S_cond.
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
 
  Goal {| a, b, c |} = S_cond.
  Proof.
    apply: Extensionality_Ensembles.
    rewrite /Same_set.
    split.
    -rewrite /S_cond.
     rewrite /Included.
     move => w.
     rewrite /In.
     move => H1.
     rewrite -or_assoc.
     apply H1.
    -rewrite /S_cond.
     rewrite /Included.
     move => w.
     rewrite /In.
     move => H1.
     rewrite or_assoc.
     apply H1.
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

End ProductSet_Example.

Require Import Coq.Lists.List.
Import List.ListNotations.

Section S1.
End S1.
