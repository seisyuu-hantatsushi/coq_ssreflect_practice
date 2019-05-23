From mathcomp Require Import ssreflect.

Require Import set_notations.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Coq.Sets.Image.

(* R2 島内剛一 数学の基礎 *)
(* R3 斎藤正彦 数学の基礎 ISBN 4-13-062909-3 *)

Section ImgExample.
  Variable U V W:Type.

  Import SetNotations.

  (* R3 1.2.4 definition *)
  Inductive InvIm (B: Ensemble V) (f:U -> V): Ensemble U :=
    InvIm_intro: forall (x:U), (f x) ∈ B -> x ∈ (InvIm B f).

  Definition Compsite (A B C : Type) (g:B -> C) (f:A -> B) : A -> C := fun (x:A) => g (f x).

  (* ℑ:Unicode 2111, 𝔪:Unicode 1D52A *)
  Notation "ℑ𝔪( f | A )" := (Im _ _ A f) (at level 60).
  Notation "ℑ𝔪^-1( f | A )" := (InvIm A f) (at level 60).
  Notation "g ・ f" := (@Compsite _ _ _ g f) (left associativity, at level 50).

  Lemma InvIm_def: forall (B: Ensemble V) (f:U -> V) (x:U),
      x ∈ (InvIm B f) -> (f x) ∈ B.
  Proof.
    move => B f x HInvIm.
    inversion HInvIm as [y HfxB].
    apply HfxB.
  Qed.

  Lemma InvIm_inv: forall (B: Ensemble V) (f:U -> V) (x:U),
      x ∈ (InvIm B f) -> (f x) ∈ B.
  Proof.
    move => B f x HInvImB.
    inversion HInvImB as [y HyB].
    exact HyB.
  Qed.

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

  (* f[A] \ f[B] ⊂ f[A \ B] *)
  Goal forall (A B:Ensemble U) (f:U -> V),
      (ℑ𝔪( f | A ) \ ℑ𝔪( f | B )) ⊂ ℑ𝔪( f | (A \ B) ).
  Proof.
    move => A B f x.
    case => HImA HnImB.
    inversion HImA as [a HaA y Hxfa Hxeqy].
    rewrite Hxfa.
    apply Im_def.
    split.
    apply HaA.
    unfold not.
    move => HaB.
    apply HnImB.
    rewrite Hxfa.
    apply Im_def.
    apply HaB.
  Qed.

  (* f^-1[C ∪ D] = f^-1[C] ∪ f^-1[D] *)
  Lemma InvIm_Union:
    forall (C D: Ensemble V) (f:U->V), ℑ𝔪^-1( f | C ∪ D ) = ℑ𝔪^-1( f | C ) ∪ ℑ𝔪^-1( f | D ).
  Proof.
    move => C D f.
    apply Extensionality_Ensembles.
    split => y H.
    inversion H as [x HyCD Hxeqy].
    inversion HyCD as [v H0|].
    left.
    split.
    apply H0.
    right.
    split.
    apply H0.
    split; inversion H; inversion H0.
    left.
    apply H2.
    right.
    apply H2.
  Qed.

  (* f^-1[C ∩ D] = f^-1[C] ∩ f^-1[D] *)
  Lemma InvIm_Intersection:
    forall (C D: Ensemble V) (f:U->V), ℑ𝔪^-1( f | C ∩ D ) = ℑ𝔪^-1( f | C ) ∩ ℑ𝔪^-1( f | D ).
  Proof.
    move => C D f.
    apply Extensionality_Ensembles.
    split => x H.
    inversion H; inversion H0 as [y].
    split; split.
    apply H2.
    apply H3.
    inversion H as [y HC HD].
    inversion HC as [w].
    inversion HD as [z].
    split; split.
    apply H1.
    apply H3.
  Qed.

  (* R2 Problem 2.3.10 *)
  Goal forall (A:Ensemble U) (f:U->V), A ⊂ ℑ𝔪^-1( f | (ℑ𝔪( f | A ))).
  Proof.
    move => A f x HA.
    split.
    apply Im_def.
    apply HA.
  Qed.

  (* B⊂X -> f(f^-1(B)) ⊂ B ∩ X *)
  Goal forall (B:Ensemble V) (f:U->V), ℑ𝔪( f | (ℑ𝔪^-1( f | B))) ⊂ (B ∩ (Full_set V)).
  Proof.
    move => B f b.
    case => x H0 y Hyfx.
    inversion H0.
    rewrite Hyfx.
    split.
    apply H.
    apply Full_intro.
  Qed.

  (* h ・ ( g ・ f ) = ( h ・ g ) ・ f *)
  Lemma compsite_assc: forall (A B C D:Type) (f:A->B) (g:B->C) (h:C->D), h ・ ( g ・ f ) = ( h ・ g ) ・ f.
  Proof.
    move => A B C D f g h.
    unfold Compsite.
    reflexivity.
  Qed.

  (* R3 Problem 1.3.1 (g ・ f)[A] = g[f[A]] *)
  Goal forall (X Y Z: Type) (A:Ensemble X) (f:X -> Y) (g:Y -> Z),
      ℑ𝔪( g ・ f | A ) = ℑ𝔪( g | ℑ𝔪( f | A )).
  Proof.
    move => X Y Z A f g.
    apply /Extensionality_Ensembles.
    split => z H.
    inversion H as [x HxA].
    rewrite H0.
    apply Im_def.
    apply Im_def.
    apply HxA.
    inversion H.
    inversion H0.
    rewrite H1.
    rewrite H4.
    have L1: forall a:X, g (f a) = (g ・ f) a.
    move => a.
    unfold Compsite.
    reflexivity.
    rewrite L1.
    apply Im_def.
    apply H3.
  Qed.

  (* R3 Problem 1.3.2 R ⊂ Z -> (g ・ f)^-1[R] = f^-1 [g^-1 [R]] *)
  
End ImgExample.
