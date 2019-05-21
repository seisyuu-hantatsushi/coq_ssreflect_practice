From mathcomp Require Import ssreflect.

Require Import set_notations.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Coq.Sets.Image.

(* R2 島内剛一 数学の基礎 *)
(* R3 斎藤正彦 数学の基礎 ISBN 4-13-062909-3 *)

Section ImgExample.
  Variable U V:Type.

  Import SetNotations.

  (* R3 1.2.4 definition *)
  Inductive InvIm (B: Ensemble V) (f:U -> V): Ensemble U :=
    InvIm_intro: forall (x:U), (f x) ∈ B -> x ∈ (InvIm B f).
  
  Notation "ℑ𝔪( f | A )" := (Im _ _ A f) (at level 60).

  Lemma Img_Subset: forall (A B:Ensemble U) (f: U -> V),
      A ⊂ B -> ℑ𝔪( f | A ) ⊂ ℑ𝔪( f | B ).
  Proof.
    move => A B f H x.
    case => s HsA y Hyfs.
    rewrite Hyfs.
    apply Im_def.
    apply H.
    apply HsA.
  Qed.

  (* R2 Problem 2.3.8 *)
  Lemma Img_Union: forall (A B:Ensemble U) (f: U -> V),
      ℑ𝔪( f | A ∪ B ) = ℑ𝔪( f | A ) ∪ ℑ𝔪( f | B ).
  Proof.
    move => A B f.
    apply /Extensionality_Ensembles.
    split => x.
    move => H.
    inversion H.
    inversion H0.
    left.
    rewrite H1.
    apply Im_def.
    apply H3.
    right.
    rewrite H1.
    apply Im_def.
    apply H3.
    case => y; case => s H z H0; rewrite H0; apply Im_def.
    left.
    apply H.
    right.
    apply H.
  Qed.

  (* R2 Problem 2.3.9 *)
  Lemma Img_Intersection: forall (A B:Ensemble U) (f: U -> V),
      ℑ𝔪( f | A ∩ B ) ⊂ ℑ𝔪( f | A ) ∩ ℑ𝔪( f | B ).
  Proof.
    move => A B f x.
    case => s.
    case => t HA HB y H0.
    rewrite H0.
    split; apply Im_def.
    apply HA.
    apply HB.
  Qed.

  Check InvIm.
  Goal forall (A:Ensemble U) (f:U->V), A ⊂ InvIm (ℑ𝔪( f | A )) f. 

End ImgExample.