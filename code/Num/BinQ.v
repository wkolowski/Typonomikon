Require Import Recdef.

(* Inductive BinQ : Type :=
| One : BinQ
| O   : BinQ -> BinQ
| I   : BinQ -> BinQ
| D   : BinQ -> BinQ.

Function succ (q : BinQ) : BinQ :=
match q with
| One  => O One
| O q' => I q'
| I q' => O (succ q')
| D q' => 


Fixpoint toQ (p q : nat) {struct p} : BinQ :=
match Nat.compare p q with
| Lt => D (toQ p (q - p))
| Eq => One
| Gt => succ (toQ (p - q) q)
end. *)