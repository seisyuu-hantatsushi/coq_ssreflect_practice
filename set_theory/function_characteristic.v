From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import function.

Section FunctionCharacteristic.
  Variable U:Type.
  Variables zero one: U.

  Definition CharacterFunction (A:Ensemble U) : Ensemble (Ensemble (Ensemble U)) := forall(f] (A × {|one|}) ∪ (A^c × {|zero|}) /\ forall (x:U), x ∈ Full_set U -> exists y:U, (|x, y|) ∈ f.

  (* Proofing uniqueness of function *)
  Goal forall (A:Ensemble U) (f:Ensemble (Ensemble (Ensemble U))), forall (x y z:U), f=CharacterFunction A -> (|x,y|) ∈ f /\ (|x,z|) ∈ f -> y = z.
  Proof.
    move => A f x y z H.
    rewrite H.
    unfold CharacterFunction.
    case => H0 H1.
    inversion H0 as [Z0|Z0]; inversion H1 as [Z1|Z1]; inversion H2; inversion H6 as [x0 [y0 [H8 [H9 H10]]]]; inversion H4; inversion H11 as [x0' [y0' [H13 [H14 H15]]]]; apply ordered_pair_iff in H10; inversion H10; apply ordered_pair_iff in H15; inversion H15; apply singleton_eq_iff in H9.
    +apply singleton_eq_iff in H14.
     rewrite H17.
     rewrite H19.
     rewrite H9.
     rewrite H14.
     reflexivity.
    +move: H13.
     case.
     rewrite -H18.
     rewrite H16.
     apply H8.
    +move: H8.
     case.
     rewrite H16 in H18.
     rewrite H18.
     apply H13.
    +apply singleton_eq_iff in H14.
     rewrite H17.
     rewrite H19.
     rewrite H9.
     rewrite H14.
     reflexivity.
  Qed.

  Goal forall (A:Ensemble U) (a:U),
      a ∈ A -> (CharacterFunction A) '' {|a|} = {|one|}.
  Proof.
    move => A a H.
    unfold CharacterFunction.
    apply /Extensionality_Ensembles.
    +split => y H0.
     inversion H0 as [y'].
     inversion H1.
     inversion H3.
     inversion H5 as [FC|FC].
     ++inversion H6.
       inversion H8 as [x0 [y0]].
       inversion H10.
       inversion H12.
       apply ordered_pair_iff in H14.
       inversion H14.
       rewrite -H16 in H13.
       apply H13.
     ++inversion H6.
       inversion H8 as [x0 [y0]].
       inversion H10.
       inversion H12.
       move : H11.
       case.
       apply ordered_pair_iff in H14.
       inversion H14.
       rewrite -H11.
       apply singleton_eq_iff in H4.
       rewrite H4.
       apply H.
    +split.
     exists a.
     split.
     done.
     left.
     split.
     exists a.
     exists y.
     split.
     apply H.
     split.
     apply H0.
     apply ordered_pair_iff.
     done.
  Qed.

  Goal forall (A:Ensemble U) (a:U),
      ~(a ∈ A) -> (CharacterFunction A) '' {|a|} = {|zero|}.
  Proof.
    move => A a H.
    unfold CharacterFunction.
    apply /Extensionality_Ensembles.
    +split => y H0.
     inversion H0 as [y'].
     inversion H1 as [x'].
     inversion H3.
     inversion H5 as [Z|Z].
     ++inversion H6.
       inversion H8 as [x0 [y0]].
       inversion H10.
       inversion H12.
       move: H.
       case.
       apply singleton_eq_iff in H4.
       rewrite -H4.
       apply ordered_pair_iff in H14.
       inversion H14.
       rewrite H.
       apply H11.
     ++inversion H6.
       inversion H8 as [x0 [y0]].
       inversion H10.
       inversion H12.
       apply ordered_pair_iff in H14.
       inversion H14.
       rewrite H16.
       apply H13.
    +split.
     exists a.
     split.
     done.
     right.
     split.
     exists a.
     exists y.
     split.
     apply H.
     split.
     apply H0.
     done.
  Qed.

  Goal forall (f:Ensemble (Ensemble (Ensemble U))) (A:Ensemble U),
      f=CharacterFunction A -> 𝕯( f ) = Full_set U.
  Proof.
    move => f A H.
    rewrite H.
    apply /Extensionality_Ensembles.
    split => x.
    move => H0.
    inversion H0.
    inversion H1.
    inversion H3 as [y].
    inversion H5 as [Z|Z]; inversion H6; inversion H8 as [x' [y']]; inversion H10; inversion H12; apply ordered_pair_iff in H14; inversion H14; rewrite H15; move: H11; done.
    move => H0.
    split.
    split.
    exists one.
    unfold CharacterFunction.
    left.
    split.
    exists x.
    exists one.
    split.

End FunctionCharacteristic.
