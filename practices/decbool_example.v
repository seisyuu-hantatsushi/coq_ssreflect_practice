From mathcomp Require Import ssreflect.

Require Import Coq.Sets.Ensembles.
Require Import Coq.Bool.DecBool.

Section Exam.
  Variable U:Type.
  Variable X:Ensemble U.
  Variable x:U.
  About ifdec.
  Check (In U X x).
  Check ({In U X x}+{~In U X x}).
  Check (ifdec ({In U X x}+{~In U X x}) bool).