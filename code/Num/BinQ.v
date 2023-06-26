Require Import Recdef.

(**
  Interpretacja:
  - [One] = 1
  - [O q] = 2q
  - [I q] = 2q + 1
  - [D q] = 1/(q + 1)
*)
Inductive BinQ : Type :=
| One : BinQ
| O   : BinQ -> BinQ
| I   : BinQ -> BinQ
| D   : BinQ -> BinQ.

Require Import FloatClass.

Require Import Floats.

Fixpoint lolwut (q : BinQ) : float :=
match q with
| One => 1
| O q' => 2 * lolwut q'
| I q' => 1 + 2 * lolwut q'
| D q' => 1 / (1 + lolwut q')
end.

(** To gunwo nie działa. *)