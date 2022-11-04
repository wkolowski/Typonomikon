Require Import Recdef Nat.

Require Import List.
Import ListNotations.

From Equations Require Import Equations.

Inductive Q : Type :=
| One : Q
| N   : Q -> Q
| D   : Q -> Q.

Unset Guard Checking.
Fixpoint euclid_sub (p q : nat) {struct p} : nat :=
match Nat.compare p q with
| Lt => euclid_sub p (q - p)
| Eq => p
| Gt => euclid_sub (p - q) q
end.

Fixpoint toQ (p q : nat) {struct p} : Q :=
match Nat.compare p q with
| Lt => D (toQ p (q - p))
| Eq => One
| Gt => N (toQ (p - q) q)
end.

Fixpoint toQFib (p q : nat) {struct p} : Q :=
match Nat.compare p q with
| Lt => D (toQFib (q - p) p)
| Eq => One
| Gt => N (toQFib (p - q) q)
end.
Set Guard Checking.

Definition toQ' (p q : nat) : option Q :=
match p, q with
| 0, _ => None
| _, 0 => None
| _, _ => Some (toQ p q)
end.

Definition toQFib' (p q : nat) : option Q :=
match p, q with
| 0, _ => None
| _, 0 => None
| _, _ => Some (toQFib p q)
end.

Function fromQ (q : Q) : nat * nat :=
match q with
| One  => (1, 1)
| N q' => let (p, q) := fromQ q' in (p + q, q)
| D q' => let (p, q) := fromQ q' in (p, q + p)
end.

Function fromQFib (q : Q) : nat * nat :=
match q with
| One  => (1, 1)
| N q' => let (p, q) := fromQFib q' in (p + q, q)
| D q' => let (p, q) := fromQFib q' in (q, q + p)
end.

Function inv (q : Q) : Q :=
match q with
| One  => One
| D q' => N (inv q')
| N q' => D (inv q')
end.

Function invFib (q : Q) : Q :=
match q with
| One => One
| N q' => D q'
| D q' => N q'
end.

Function cmp (q1 q2 : Q) : comparison :=
match q1, q2 with
| One  , One   => Eq
| One  , D _   => Gt
| One  , N _   => Lt
| D _  , One   => Lt
| D q1', D q2' => cmp q1' q2'
| D _  , N _   => Lt
| N _  , One   => Gt
| N _  , D _   => Gt
| N q1', N q2' => cmp q1' q2'
end.

(* Definition fromQFib (q : Q) : nat * nat :=
  let (n, m) := fromQ q in (n - 1, m - 1). *)

Definition qpadd (q1 q2 : Q) : Q :=
  let (n1, m1) := fromQ q1 in
  let (n2, m2) := fromQ q2 in
    toQ (n1 * m2 + n2 * m1) (m1 * m2).

Definition qpmul (q1 q2 : Q) : Q :=
match fromQ q1, fromQ q2 with
| (n1, m1), (n2, m2) => toQ (n1 * n2) (m1 * m2)
end.

Fixpoint iter (n : nat) {A : Type} (f : A -> A) (x : A) : A :=
match n with
| 0 => x
| S n' => f (iter n' f x)
end.

Compute toQ 0 0.
(* Compute toQ 1 0. *) (* Diverges *)
(* Compute toQ 0 1. *) (* Diverges *)
Compute toQ 1 1.

Compute toQ' 0 0.
Compute toQ' 1 0.
Compute toQ' 0 1.
Compute toQ' 1 1.

Compute toQ' 11 5.

Compute map (fun n => toQ 1 (n + 1)) [0; 1; 2; 3; 4; 5; 6; 7; 8; 9].
Compute map (fun n => toQ n (n + 1)) [1; 2; 3; 4; 5; 6; 7; 8; 9].
Compute map (fun n => toQ n (2 * n)) [1; 2; 3; 4; 5; 6; 7; 8; 9].
Compute map (fun n => toQ 1 (pow 2 n)) [0; 1; 2; 3; 4].
Compute map (fun n => toQ 1 (pow 2 n)) [0; 1; 2; 3; 4].

Compute map (fun n => fromQ (iter n N One)) [0; 1; 2; 3; 4; 5; 6; 7; 8; 9].
Compute map (fun n => fromQ (iter n D One)) [0; 1; 2; 3; 4; 5; 6; 7; 8; 9].

Compute map (fun n => fromQ (inv (toQ 1 (n + 1)))) [0; 1; 2; 3; 4; 5; 6; 7; 8; 9].
Compute map (fun n => fromQ (inv (toQ n (n + 1)))) [1; 2; 3; 4; 5; 6; 7; 8; 9].
Compute map (fun n => fromQ (inv (toQ n (2 * n)))) [1; 2; 3; 4; 5; 6; 7; 8; 9].
Compute map (fun n => fromQ (inv (toQ 1 (pow 2 n)))) [0; 1; 2; 3; 4].

Compute fromQ (inv (toQ 12 5)).

Compute toQFib 0 0.
(* Compute toQFib 1 0. *) (* Diverges *)
(* Compute toQFib 0 1. *) (* Diverges *)
Compute toQFib 1 1.

Compute toQFib' 0 0.
Compute toQFib' 1 0.
Compute toQFib' 0 1.
Compute toQFib' 1 1.

Compute toQFib' 11 5.

Compute map (fun n => toQFib 1 (n + 1)) [0; 1; 2; 3; 4; 5; 6; 7; 8; 9].
Compute map (fun n => toQFib n (n + 1)) [1; 2; 3; 4; 5; 6; 7; 8; 9].
Compute map (fun n => toQFib n (2 * n)) [1; 2; 3; 4; 5; 6; 7; 8; 9].
Compute map (fun n => toQFib 1 (pow 2 n)) [0; 1; 2; 3; 4].

Compute map (fun n => fromQFib (iter n N One)) [0; 1; 2; 3; 4; 5; 6; 7; 8; 9].
Compute map (fun n => fromQFib (iter n D One)) [0; 1; 2; 3; 4; 5; 6; 7; 8; 9].

Compute fromQFib (inv (toQFib 12 5)).

Lemma inv_inv :
  forall q : Q,
    inv (inv q) = q.
Proof.
  intros q; functional induction (inv q); cbn; rewrite ?IHq0; reflexivity.
Qed.

Lemma cmp_inv :
  forall q1 q2 : Q,
    cmp (inv q1) (inv q2) = CompOpp (cmp q1 q2).
Proof.
  intros q1 q2.
  functional induction (cmp q1 q2); cbn; rewrite ?IHc; try reflexivity.
Qed.

Lemma cmp_inv' :
  forall q1 q2 : Q,
    cmp (inv q1) (inv q2) = cmp q2 q1.
Proof.
  intros q1 q2.
  functional induction (cmp q1 q2); cbn; rewrite ?IHc; try reflexivity.
Qed.

Lemma toQ_eq :
  forall p q : nat,
    toQ p q
      =
    match Nat.compare p q with
    | Lt => D (toQ p (q - p))
    | Eq => One
    | Gt => N (toQ (p - q) q)
    end.
Proof.
Admitted.

Lemma toQ'_eq :
  forall p q : nat,
    toQ' p q
      =
    match p, q with
    | 0, _ => None
    | _, 0 => None
    | _, _ =>
      match Nat.compare p q with
      | Lt => option_map D (toQ' p (q - p))
      | Eq => Some One
      | Gt => option_map N (toQ' (p - q) q)
      end
    end.
Proof.
  destruct p as [| p'], q as [| q'].
  1-3: reflexivity.
  - destruct (Nat.compare (S p') (S q')) eqn: Heq.
Admitted.

Inductive Q' : Set :=
| Qneg  : Q' -> Q'
| Qzero : Q'
| Qpos  : Q' -> Q'.

(** TODO: rozszerzyć operacje na [Q] na całe [Q]. *)

Definition qneg (q : Q') : Q' :=
match q with
| Qneg q' => Qpos q'
| Qzero   => Qzero
| Qpos q' => Qneg q'
end.