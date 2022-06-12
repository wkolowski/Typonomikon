Require Import Recdef.

(** [I'] to 1, [O k] to 2k, zaś [I k] to 2k + 1. *)
Inductive Pos : Set :=
| I' : Pos
| O : Pos -> Pos
| I : Pos -> Pos.

Definition One : Pos := I'.

Fixpoint toNat (n : Pos) : nat :=
match n with
| I' => 1
| O n' => 2 * toNat n'
| I n' => 1 + 2 * toNat n'
end.

Compute toNat (O (O (O I'))).

Function succ (p : Pos) : Pos :=
match p with
| I'    => O I'
| O p' => I p'
| I p' => O (succ p')
end.

Compute succ (I (I (I I'))).
Compute toNat (I (I (I I'))).
Compute toNat (succ (I (I (I I')))).

Function pred (p : Pos) : Pos :=
match p with
| I'   => I'
| O p' => O (pred p')
| I p' => O p'
end.

Compute pred (I (I (I I'))).
Compute toNat (I (I (I I'))).
Compute toNat (pred (I (I (I I')))).

Function pred' (p : Pos) : option Pos :=
match p with
| I'    => None
| O p' => option_map O (pred' p')
| I p' => Some (O p')
end.

Compute pred' (I (I (I I'))).
Compute toNat (I (I (I I'))).
Compute option_map toNat (pred' (I (I (I I')))).

Function add (p1 p2 : Pos) : Pos :=
match p1, p2 with
| I'    , _     => succ p2
| _    , I'     => succ p1
| O p1', O p2' => O (add p1' p2')
| O p1', I p2' => I (add p1' p2')
| I p1', O p2' => I (add p1' p2')
| I p1', I p2' => O (succ (add p1' p2'))
end.

Compute add (I (I (I I'))) (I (O (I I'))).
Compute toNat (I (I (I I'))).
Compute toNat (I (O (I I'))).
Compute toNat (add (I (I (I I'))) (I (O (I I')))).

(* Function sub (p1 p2 : Pos) : option Pos :=
match p1, p2 with
end. *)

Function double' (p : Pos) : Pos :=
match p with
| I'    => O I'
| O p' => O (double' p')
| I p' => O (succ (double' p'))
end.

Definition double (p : Pos) := O p.

Compute double (I (I (I I'))).
Compute toNat (I (I (O I'))).
Compute toNat (double (I (I (O I')))).

Function mul (p1 p2 : Pos) : Pos :=
match p1 with
| I'     => p2
| O p1' => mul p1' (O p2)
| I p1' => add p2 (mul p1' (O p2))
end.

Compute mul (I (I (I I'))) (I (O (I I'))).
Compute toNat (I (I (I I'))).
Compute toNat (I (O (I I'))).
Compute toNat (mul (I (I (I I'))) (I (O (I I')))).

(* Function pow (p1 p2 : Pos) : Pos :=
match p2 with
end. *)

Function compare (p1 p2 : Pos) : comparison :=
match p1, p2 with
| I'    , I'     => Eq
| I'    , _     => Lt
| _    , I'     => Gt
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

Compute compare (I (I (I I'))) (I (O (I I'))).
Compute toNat (I (I (I I'))).
Compute toNat (I (O (I I'))).
Compute Nat.compare (toNat (I (I (I I')))) (toNat (I (O (I I')))).

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
| I'   => true
| O _ => false
| I _ => true
end.

Definition even (p : Pos) : bool := negb (odd p).

Lemma add_I'_r :
  forall p : Pos,
    add p I' = succ p.
Proof.
  destruct p; cbn; reflexivity.
Qed.

Lemma add_succ_l :
  forall p1 p2 : Pos,
    add (succ p1) p2 = succ (add p1 p2).
Proof.
  intros p1.
  functional induction succ p1; cbn; intros.
  - destruct p2; cbn; reflexivity.
  - destruct p2; cbn; reflexivity.
  - destruct p2; cbn; rewrite ?IHp; reflexivity.
Qed.

Lemma add_comm :
  forall p1 p2 : Pos,
    add p1 p2 = add p2 p1.
Proof.
  intros p1 p2.
  functional induction add p1 p2
  ; cbn; rewrite ?IHp; try reflexivity.
  rewrite add_I'_r; reflexivity.
Qed.

Lemma add_succ_r :
  forall p1 p2 : Pos,
    add p1 (succ p2) = succ (add p1 p2).
Proof.
  intros p1 p2.
  rewrite add_comm, add_succ_l, <- add_comm.
  reflexivity.
Qed.

Lemma add_assoc :
  forall p1 p2 p3 : Pos,
    add (add p1 p2) p3 = add p1 (add p2 p3).
Proof.
  intros p1 p2.
  functional induction add p1 p2; cbn; intros p3.
  - rewrite add_succ_l; reflexivity.
  - rewrite add_succ_l, add_succ_r. reflexivity.
  - destruct p3; cbn; rewrite ?IHp; reflexivity.
  - destruct p3; cbn; rewrite ?add_succ_l, ?add_succ_r, ?IHp; reflexivity.
  - destruct p3; cbn; rewrite ?add_succ_l, ?add_succ_r, ?IHp; reflexivity.
  - destruct p3; cbn; rewrite ?add_succ_l, ?add_succ_r, ?IHp; reflexivity.
Admitted.

Lemma mul_comm :
  forall p1 p2 : Pos,
    mul p1 p2 = mul p2 p1.

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