Require Import Recdef.

(** [H] to 1, [O k] to 2k, zaś [I k] to 2k + 1. *)
Inductive Pos : Set :=
| H : Pos
| O : Pos -> Pos
| I : Pos -> Pos.

Fixpoint toNat (n : Pos) : nat :=
match n with
    | H => 1
    | O n' => 2 * toNat n'
    | I n' => 1 + 2 * toNat n'
end.

Compute toNat (O (O (O H))).

Function succ (p : Pos) : Pos :=
match p with
| H    => O H
| O p' => I p'
| I p' => O (succ p')
end.

Compute succ (I (I (I H))).
Compute toNat (I (I (I H))).
Compute toNat (succ (I (I (I H)))).

Function add (p1 p2 : Pos) : Pos :=
match p1, p2 with
| H    , _     => succ p2
| _    , H     => succ p1
| O p1', O p2' => O (add p1' p2')
| O p1', I p2' => I (add p1' p2')
| I p1', O p2' => I (add p1' p2')
| I p1', I p2' => O (succ (add p1' p2'))
end.

Compute add (I (I (I H))) (I (O (I H))).
Compute toNat (I (I (I H))).
Compute toNat (I (O (I H))).
Compute toNat (add (I (I (I H))) (I (O (I H)))).

Function pred (p : Pos) : option Pos :=
match p with
| H    => None
| O p' => option_map O (pred p')
| I p' => Some (O p')
end.

Compute pred (I (I (I H))).
Compute toNat (I (I (I H))).
Compute option_map toNat (pred (I (I (I H)))).

(* Function sub (p1 p2 : Pos) : option Pos :=
match p1, p2 with
end. *)

Function double' (p : Pos) : Pos :=
match p with
| H    => O H
| O p' => O (double' p')
| I p' => O (succ (double' p'))
end.

Definition double (p : Pos) := O p.

Compute double (I (I (I H))).
Compute toNat (I (I (O H))).
Compute toNat (double (I (I (O H)))).

Function mul (p1 p2 : Pos) : Pos :=
match p1 with
| H     => p2
| O p1' => mul p1' (O p2)
| I p1' => add p2 (mul p1' (O p2))
end.

Compute mul (I (I (I H))) (I (O (I H))).
Compute toNat (I (I (I H))).
Compute toNat (I (O (I H))).
Compute toNat (mul (I (I (I H))) (I (O (I H)))).

(* Function pow (p1 p2 : Pos) : Pos :=
match p2 with
end. *)

Function compare (p1 p2 : Pos) : comparison :=
match p1, p2 with
| H    , H     => Eq
| H    , _     => Lt
| _    , H     => Gt
| O p1', O p2' => compare p1' p2'
| O p1', I p2' =>
  match compare p1' p2' with
  | Lt => Lt
  | Eq => Lt
  | Gt => Gt
  end
| I p1', O p2' =>
  match compare p1' p2' with
  | Lt => Lt
  | Eq => Gt
  | Gt => Gt
  end
| I p1', I p2' => compare p1' p2'
end.

Compute compare (I (I (I H))) (I (O (I H))).
Compute toNat (I (I (I H))).
Compute toNat (I (O (I H))).
Compute Nat.compare (toNat (I (I (I H)))) (toNat (I (O (I H)))).

Definition eqb (p1 p2 : Pos) : bool :=
match compare p1 p2 with
| Eq => true
| _  => false
end.

Definition leb (p1 p2 : Pos) : bool :=
match compare p1 p2 with
| Gt => false
| _  => true
end.

Definition ltb (p1 p2 : Pos) : bool :=
match compare p1 p2 with
| Lt => true
| _  => false
end.

Definition max (p1 p2 : Pos) : Pos :=
match compare p1 p2 with
| Lt => p2
| _  => p1
end.

Definition min (p1 p2 : Pos) : Pos :=
match compare p1 p2 with
| Lt => p1
| _  => p2
end.

Function odd (p : Pos) : bool :=
match p with
| H   => true
| O _ => false
| I _ => true
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