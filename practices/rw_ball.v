Inductive RWball : Set :=
        | rball
        | wball.

Print list.

Inductive balllist : Type :=
| nil : balllist
| cons : RWball -> balllist -> balllist.

Check nil.
Check rball.
Check cons rball nil.
(* Check nil cons rball nil. *)
Check cons (wball) (cons rball nil).

Fixpoint countRball (l:balllist) : nat :=
  match l with
  | nil => 0
  | cons rball t => 1 + (countRball t)
  | cons wball t => (countRball t)
  end.

Compute countRball  nil.
Compute countRball  (cons rball nil).
Compute countRball  (cons wball nil).
Compute countRball  (cons rball (cons rball nil)).
Compute countRball  (cons rball (cons wball nil)).

