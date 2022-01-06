From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import function.

Section FunctionCharacteristic.
  Variable U:Type.
  Variables zero one: U.

  Definition CharacterFunction (A:Ensemble U) (f:Ensemble (Ensemble (Ensemble U))) :=
    f = (A × {|one|}) ∪ (A^c × {|zero|}) /\ forall (x:U), x ∈ Full_set U -> exists y:U, (|x, y|) ∈ f.

  (* Proofing uniqueness of function *)
  Goal forall (A:Ensemble U) (f:Ensemble (Ensemble (Ensemble U))) (x y z:U), CharacterFunction A f -> (|x,y|) ∈ f /\ (|x,z|) ∈ f -> y = z.
  Proof.
    move => A f x y z.
    unfold CharacterFunction.
    case => H H0.
    rewrite H.
    move => H1.
    inversion H1.
    inversion H2 as [Z0|Z0]; inversion H3 as [Z1|Z1]; inversion H4; inversion H8 as [x0 [y0 [H10 [H11 H12]]]]; inversion H6; inversion H13 as [x0' [y0' [H15 [H16 H17]]]]; apply ordered_pair_iff in H12; inversion H12; apply ordered_pair_iff in H17; inversion H17; apply singleton_eq_iff in H11.
    +apply singleton_eq_iff in H16.
     rewrite H19.
     rewrite H21.
     rewrite H11.
     rewrite H16.
     reflexivity.
    +move: H15.
     case.
     rewrite -H20.
     rewrite H18.
     apply H10.
    +move: H10.
     case.
     rewrite -H18.
     rewrite H20.
     apply H15.
    +apply singleton_eq_iff in H16.
     rewrite H19.
     rewrite H21.
     rewrite H11.
     rewrite H16.
     reflexivity.
  Qed.

  Goal forall (A:Ensemble U) (a:U) (f:Ensemble (Ensemble (Ensemble U))),
      a ∈ A /\ (CharacterFunction A f) -> f '' {|a|} = {|one|}.
  Proof.
    move => A a f.
    unfold CharacterFunction.
    case => H [Hf HfS].
    rewrite Hf.
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

  Goal forall (A:Ensemble U) (a:U) (f:Ensemble (Ensemble (Ensemble U))),
      ~(a ∈ A) /\ (CharacterFunction A f) -> f '' {|a|} = {|zero|}.
  Proof.
    move => A a f.
    unfold CharacterFunction.
    case => H [Hf HfS].
    rewrite Hf.
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
      CharacterFunction A f -> 𝕯( f ) = Full_set U.
  Proof.
    unfold CharacterFunction.
    move => f A.
    case => H HfS.
    rewrite H.
    apply /Extensionality_Ensembles.
    split => x.
    +move => H0.
     inversion H0.
     inversion H1.
     inversion H3 as [y].
     inversion H5 as [Z|Z]; inversion H6; inversion H8 as [x' [y']]; inversion H10; inversion H12; apply ordered_pair_iff in H14; inversion H14; rewrite H15; move: H11; done.
    +move => H0.
     split.
     split.
     rewrite -H.
     apply HfS.
     apply H0.
  Qed.

  Goal forall (a b c:U) (A:Ensemble U) (f:Ensemble (Ensemble (Ensemble U))),
      A={|a,b,c|} /\ CharacterFunction A f -> f '' {|a|} = {|one|}.
  Proof.
    move => a b c A f.
    case => H [Hf HfS].
    rewrite Hf.
    -apply /Extensionality_Ensembles.
     split => y H0.
     +inversion H0.
      inversion H1.
      inversion H3.
      inversion H5 as [Z|Z]; inversion H6; inversion H8 as [x' [y' H10]]; inversion H10;inversion H12; apply ordered_pair_iff in H14;inversion H14.
      ++rewrite H16.
        apply H13.
      ++move: H11.
        case.
        rewrite -H15.
        rewrite H.
        left.
        left.
        apply H4.
     +split.
      exists a.
      split.
      done.
      left.
      split.
      exists a.
      exists one.
      split.
      ++rewrite H.
        left.
        left.
        done.
      ++split.
        done.
      ++apply ordered_pair_iff.
        split.
        reflexivity.
        apply singleton_eq_iff.
        apply H0.
  Qed.

End FunctionCharacteristic.
