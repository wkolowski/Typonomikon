Require Import Recdef Lia.

Require Import List.
Import ListNotations.

From Equations Require Import Equations.

From Typonomikon Require Import UnaryPos.

Inductive Q : Type :=
| One : Q
| N   : Q -> Q
| D   : Q -> Q.

Coercion fromNat : nat >-> Pos.

Function euclid_sub (pq : Pos * Pos) {measure (fun '(p, q) => toNat p + toNat q) pq} : Pos :=
let '(p, q) := pq in
match UnaryPos.compare p q with
| Lt => euclid_sub (p, sub' q p)
| Eq => p
| Gt => euclid_sub (sub' p q, q)
end.
Proof.
  - intros pq p q -> Hcmp.
    functional induction sub' q p; cbn.
    + functional inversion Hcmp.
    + lia.
    + rewrite UnaryPos.compare_succ in Hcmp; specialize (IHp0 Hcmp); lia.
  - intros pq p q -> Hcmp.
    functional induction sub' p q; cbn.
    + functional inversion Hcmp.
    + lia.
    + rewrite UnaryPos.compare_succ in Hcmp; specialize (IHp0 Hcmp); lia.
Defined.

Definition euclid_sub' p q := euclid_sub (p, q).

Compute euclid_sub' 6 8.

Unset Guard Checking.
Fixpoint toQ (p q : Pos) {struct p} : Q :=
match UnaryPos.compare p q with
| Lt => D (toQ p (sub' q p))
| Eq => One
| Gt => N (toQ (sub' p q) q)
end.

Fixpoint toQFib (p q : Pos) {struct p} : Q :=
match UnaryPos.compare p q with
| Lt => D (toQFib (sub' q p) p)
| Eq => One
| Gt => N (toQFib (sub' p q) q)
end.
Set Guard Checking.

Function fromQ (q : Q) : Pos * Pos :=
match q with
| One  => (UnaryPos.One, UnaryPos.One)
| N q' => let (p, q) := fromQ q' in (add p q, q)
| D q' => let (p, q) := fromQ q' in (p, add q p)
end.

Function fromQFib (q : Q) : Pos * Pos :=
match q with
| One  => (UnaryPos.One, UnaryPos.One)
| N q' => let (p, q) := fromQFib q' in (add p q, q)
| D q' => let (p, q) := fromQFib q' in (q, add q p)
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
    toQ (UnaryPos.add (UnaryPos.mul n1 m2) (UnaryPos.mul n2 m1))
        (UnaryPos.mul m1 m2).

Definition qpmul (q1 q2 : Q) : Q :=
match fromQ q1, fromQ q2 with
    | (n1, m1), (n2, m2) => toQ (UnaryPos.mul n1 n2) (UnaryPos.mul m1 m2)
end.

Fixpoint iter (n : nat) {A : Type} (f : A -> A) (x : A) : A :=
match n with
| 0 => x
| Datatypes.S n' => f (iter n' f x)
end.

Compute (toQ UnaryPos.One UnaryPos.One).

Compute toQ (UnaryPos.fromNat 11) (UnaryPos.fromNat 5).

Compute map (fun n : nat => toQ 1 (n + 1)) [0; 1; 2; 3; 4; 5; 6; 7; 8; 9].
Compute map (fun n : nat => toQ n (n + 1)) [1; 2; 3; 4; 5; 6; 7; 8; 9].
Compute map (fun n : nat => toQ n (2 * n)) [1; 2; 3; 4; 5; 6; 7; 8; 9].
Compute map (fun n : nat => toQ 1 (pow 2 n)) [0; 1; 2; 3; 4].
Compute map (fun n : nat => toQ 1 (pow 2 n)) [0; 1; 2; 3; 4].

Compute map (fun n : nat => fromQ (iter n N One)) [0; 1; 2; 3; 4; 5; 6; 7; 8; 9].
Compute map (fun n : nat => fromQ (iter n D One)) [0; 1; 2; 3; 4; 5; 6; 7; 8; 9].

Compute map (fun n : nat => fromQ (inv (toQ 1 (n + 1)))) [0; 1; 2; 3; 4; 5; 6; 7; 8; 9].
Compute map (fun n : nat => fromQ (inv (toQ n (n + 1)))) [1; 2; 3; 4; 5; 6; 7; 8; 9].
Compute map (fun n : nat => fromQ (inv (toQ n (2 * n)))) [1; 2; 3; 4; 5; 6; 7; 8; 9].
Compute map (fun n : nat => fromQ (inv (toQ 1 (pow 2 n)))) [0; 1; 2; 3; 4].

Compute fromQ (inv (toQ 12 5)).

Compute toQFib 1 1.

Compute toQFib 11 5.

Compute map (fun n : nat => toQFib 1 (n + 1)) [0; 1; 2; 3; 4; 5; 6; 7; 8; 9].
Compute map (fun n : nat => toQFib n (n + 1)) [1; 2; 3; 4; 5; 6; 7; 8; 9].
Compute map (fun n : nat => toQFib n (2 * n)) [1; 2; 3; 4; 5; 6; 7; 8; 9].
Compute map (fun n : nat => toQFib 1 (pow 2 n)) [0; 1; 2; 3; 4].

Compute map (fun n : nat => fromQFib (iter n N One)) [0; 1; 2; 3; 4; 5; 6; 7; 8; 9].
Compute map (fun n : nat => fromQFib (iter n D One)) [0; 1; 2; 3; 4; 5; 6; 7; 8; 9].

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
  intros p q.
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