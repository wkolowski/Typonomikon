Require Import Recdef.

Inductive Pos : Type :=
| One : Pos
| S   : Pos -> Pos.

Function add (p1 p2 : Pos) : Pos :=
match p1 with
| One   => S p2
| S p1' => S (add p1' p2)
end.

Function pred (p : Pos) : option Pos :=
match p with
| One => None
| S p1' => Some p1'
end.

Function sub (p1 p2 : Pos) : option Pos :=
match p1, p2 with
| One  , _    => None
| S p1', One  => Some p1'
| S p1', S p2' => sub p1' p2'
end.

Function double (p : Pos) : Pos :=
match p with
| One   => S One
| S p1' => S (S (double p1'))
end.

Function mul (p1 p2 : Pos) : Pos :=
match p1 with
| One   => p2
| S p1' => add p2 (mul p1' p2)
end.

Function pow (p1 p2 : Pos) : Pos :=
match p2 with
| One   => p1
| S p2' => mul p1 (pow p1 p2')
end.

Function max (p1 p2 : Pos) : Pos :=
match p1, p2 with
| One  , _     => p2
| _    , One   => p1
| S p1', S p2' => S (max p1' p2')
end.

Function min (p1 p2 : Pos) : Pos :=
match p1, p2 with
| One  , _     => One
| _    , One   => One
| S p1', S p2' => S (min p1' p2')
end.

Function compare (p1 p2 : Pos) : comparison :=
match p1, p2 with
| One  , One   => Eq
| One  , S _   => Lt
| S _  , One   => Gt
| S p1', S p2' => compare p1' p2'
end.

Function eqb (p1 p2 : Pos) : bool :=
match p1, p2 with
| One  , One   => true
| S p1', S p2' => eqb p1' p2'
| _    , _     => false
end.

Function leb (p1 p2 : Pos) : bool :=
match p1, p2 with
| One  , _     => true
| _    , One   => false
| S p1', S p2' => leb p1' p2'
end.

Function ltb (p1 p2 : Pos) : bool :=
match p1, p2 with
| _    , One   => false
| One  , S _   => true
| S p1', S p2' => ltb p1' p2'
end.

Function odd (p : Pos) : bool :=
match p with
| One   => true
| S p1' => negb (odd p1')
end.

Definition even (p : Pos) : bool := negb (odd p).

(* TODO
     Definition tail_add : nat -> nat -> nat.
     Definition tail_addmul : nat -> nat -> nat -> nat.
     Definition tail_mul : nat -> nat -> nat.

     Definition divmod : nat -> nat -> nat -> nat -> nat * nat.
     Definition div : nat -> nat -> nat.
     Definition modulo : nat -> nat -> nat.
     Definition gcd : nat -> nat -> nat.
     Definition square : nat -> nat.
     Definition sqrt_iter : nat -> nat -> nat -> nat -> nat.
     Definition sqrt : nat -> nat.
     Definition log2_iter : nat -> nat -> nat -> nat -> nat.
     Definition log2 : nat -> nat.
     Definition iter : nat -> forall A : Type, (A -> A) -> A -> A.
     Definition div2 : nat -> nat.
     Definition testbit : nat -> nat -> bool.
     Definition shiftl :
       (fun _ : nat => nat) 0 -> forall n : nat, (fun _ : nat => nat) n.
     Definition shiftr :
       (fun _ : nat => nat) 0 -> forall n : nat, (fun _ : nat => nat) n.
     Definition bitwise : (bool -> bool -> bool) -> nat -> nat -> nat -> nat.
     Definition land : nat -> nat -> nat.
     Definition lor : nat -> nat -> nat.
     Definition ldiff : nat -> nat -> nat.
     Definition lxor : nat -> nat -> nat.

 *)