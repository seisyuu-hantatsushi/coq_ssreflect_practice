From mathcomp Require Import ssreflect.

Require Import img_example.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* R1 斎藤毅   集合と位相 ISBN 978-4-13-062958-4 *)
(* R2 島内剛一 数学の基礎 *)
(* R3 斎藤正彦 数学の基礎 ISBN 4-13-062909-3 *)

Section MapExample.

  Variables U:Type.
  Variables A B: Ensemble U.


  