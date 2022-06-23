Require Import Recdef Arith Lia.

From Equations Require Import Equations.

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
| ng_0_r : forall n   : nat, norm_graph n 0 (S n, 0)
| ng_S_S : forall (n m : nat) (r : nat * nat), norm_graph n m r -> norm_graph (S n) (S m) r.

(* Wykres po usunięciu indeksów i zamianie [Prop] na [Type]. *)
(*
Inductive NG : Type :=
| ng_0_l' : forall m : nat, NG
| ng_0_r' : forall n : nat, NG
| ng_S_S' : forall (n m : nat) (r : nat * nat), NG -> NG.
*)

(* Usuwamy argumenty konstruktorów, które występowały w indeksach. *)
Inductive NG : Type :=
| ng_0_l' : NG
| ng_0_r' : NG
| ng_S_S' : NG -> NG.

(* Dlaczego powstały typ mamy interpretować tak a nie inaczej? Może tak:
   - przypadek (0, m) pokrywa (0, 0), a zatem po usunięciu indeksów
     pierwszy konstruktor powinniśmy interpretować jako zero
   - przypadek (S n, 0) nie pokrywa zera, ale za to pokrywa 1, a zatem
     po usunięciu indeksów powinniśmy go interpretować jako 1
   - ostatni przypadek jest rekurencyjny. Powinniśmy go interpretować jako
     następnik lub poprzednik, ale nie wiemy który przypadek zachodzi, więc
     interpretujemy jako następniko-poprzednik (śmieszna nazwa: cesor). *)

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
| Lt => euclid_mod (q mod p) q
| Eq => p
| Gt => euclid_mod p (p mod q)
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
Compute euclid_mod 2 4.

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

Module FM.

Inductive FM (A : Type) : Type :=
| inj : A -> FM A
| id  : FM A
| op  : FM A -> FM A -> FM A.

Arguments inj {A} _.
Arguments id  {A}.
Arguments op  {A} _ _.

Function size {A : Type} (x : FM A) : nat :=
match x with
| inj _  => 1
| id     => 1
| op l r => 1 + size l + size r
end.

(* Function norm {A : Type} (x : FM A) {measure size x} : FM A :=
match x with
| inj a  => op (inj a) id
| id     => id
| op l r =>
  match norm l with
  | inj a    => op (inj a) (norm r)
  | id       => norm r
  | op ll lr => op ll (norm (op lr r))
  end
end.
Proof.
  - intros; subst; cbn; lia.
  - intros; subst; cbn; lia.
  - intros; subst; cbn. admit.
  - intros; subst; cbn; lia.
Abort. *)

Equations norm {A : Type} (x : FM A) : FM A by wf (size x) lt :=
| inj a  => op (inj a) id
| id     => id
| op l r with (norm l) =>
  | inj a    => op (inj a) (norm r)
  | id       => norm r
  | op ll lr => op ll (norm (op lr r)).
Next Obligation. lia. Qed.
Next Obligation. lia. Qed.
Next Obligation. lia. Qed.
Next Obligation. Admitted.

Compute norm (op ((op (op (op (inj 5) (inj 2)) (inj 1)) (inj 12))) id).

End FM.