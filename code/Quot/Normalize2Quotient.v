Require Import Recdef Arith.

Module WeirdZ.

(* Funkcja normalizująca. *)
Function norm (n m : nat) : nat * nat :=
match n, m with
| 0   , _ => (0, m)
| _   , 0 => (n, 0)
| S n', S m' => norm n' m'
end.

(* Wykres funkcji. *)
Inductive norm_graph : nat -> nat -> nat * nat -> Prop :=
| ng_0_l : forall   m : nat, norm_graph 0 m (0, m)
| ng_0_r : forall n   : nat, norm_graph n 0 (n, 0)
| ng_S_S : forall (n m : nat) (r : nat * nat), norm_graph (S n) (S m) r -> norm_graph n m r.

(* Wykres po usunięciu indeksów i zamianie [Prop] na [Type]. *)
(*
Inductive NG : Type :=
| ng_0_l' : forall m : nat, NG
| ng_0_r' : forall n : nat, NG
| ng_S_S' : forall (n m : nat) (r : nat * nat), NG -> NG.
*)

(* Usuwamy argumenty konstrktorów, które występowały w indeksach. *)
Inductive NG : Type :=
| ng_0_l' : NG
| ng_0_r' : NG
| ng_S_S' : NG -> NG.

(* Dlaczego powstały typ mamy interpretować tak a nie inaczej? *)
Inductive Z : Type :=
| Zero : Z
| One : Z
| Next : Z -> Z.

End WeirdZ.

Module Qplus.

Unset Guard Checking.
Fixpoint euclid_sub (p q : nat) {struct p} : nat :=
match Nat.compare p q with
    | Lt => euclid_sub p (q - p)
    | Eq => p
    | Gt => euclid_sub (p - q) q
end.

Definition norm_sub (p q : nat) : nat * nat :=
  let gcd := euclid_sub p q in (Nat.div p gcd, Nat.div q gcd).

Fixpoint euclid_mod (p q : nat) {struct p} : nat :=
match Nat.compare p q with
    | Lt => euclid_mod q (q mod p)
    | Eq => 1
    | Gt => euclid_mod (p mod q) p
end.

Fixpoint norm (p q : nat) {struct p} : nat * nat :=
match Nat.compare p q with
    | Lt => let (p', q') := norm p (q - p) in (p', q' + p)
    | Eq => (1, 1)
    | Gt => let (p', q') := norm (p - q) q in (p' + q, q')
end.

Fixpoint extendedEu (p q : nat) {struct q} : nat * nat :=
match q with
| 0 => (1, 0)
| _ =>
  let quot := Nat.div p q in
  let rem  := p - quot * q in
  let '(s, t) := extendedEu q rem in
    (t, s - quot * t)
end.
Set Guard Checking.

Compute euclid_sub 5 10.

Compute norm_sub 2 8.

Compute extendedEu 6 9.

Compute Nat.div 10 15.
Compute Nat.modulo 15 10.

(* Inductive euclid_sub_graph : nat -> nat -> (p q : nat) {struct p} : nat :=
match Nat.compare p q with
    | Lt => euclid_sub p (q - p)
    | Eq => 1
    | Gt => euclid_sub (p - q) q
end. *)

End Qplus.