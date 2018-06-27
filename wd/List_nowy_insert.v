Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

(* begin hide *)
Fixpoint insert'
  {A : Type} (l : list A) (n : nat) (x : A) : option (list A) :=
match l, n with
    | [], _ => None
    | h :: t, 0 => Some (x :: h :: t)
    | h :: t, S n' =>
        match insert' t n' x with
            | None => None
            | Some l => Some (h :: l)
        end
end.
(* end hide *)

Compute insert' (iterate S 5 0) 4 42.