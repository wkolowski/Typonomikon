Require Import Setoid Arith Lia.

Section reverse.

Context
  (f : nat -> nat)
  (Hzero : f 0 = 0)
  (Hincreasing : forall m n, m < n -> f m < f n).

(** **** Ćwiczenie *)

(** Udowodnij, że przy powyższych założeniach dla każdego [y : nat] istnieje [x : nat]
    takie, że [f x <= y <= f (S x)]. Zdefiniuj w tym celu funkcję [g : nat -> nat] i
    udowodnij, że spełnia ona specyfikację. *)

(** **** Rozwiązanie *)

(** Definicja jest prosta:
    - jeżeli [y] to [0], to zwróć [0]
    - jeżeli [x] który znaleźliśmy dla [y - 1] jest dalej ok, to zwróć [x]
    - w przeciwnym wypadku zwróć [x + 1] *)

Fixpoint g (y : nat) : nat :=
match y with
    | 0 => 0
    | S y' =>
        let x := g y' in 
          if Nat.ltb y (f (S x))
          then x
          else S x
end.

(** Dowód też jest prosty i ma taki sam kształt jak definicja funkcji [g]. *)
Lemma g_correct : forall y (x := g y), f x <= y < f (S x).
Proof.
  induction y as [| y']; simpl.
    split.
      rewrite Hzero. apply le_n.
      rewrite <- Hzero at 1. apply Hincreasing. lia.
    destruct (Nat.ltb_spec (S y') (f (S (g y')))).
      split.
        destruct IHy'. lia.
        assumption.
      split.
        assumption.
        destruct IHy'. assert (f (S (g y')) < f (S (S (g y')))).
          apply Hincreasing. lia.
          lia.
Qed.

(** Uwaga: komenda [Function] nie upraszcza powyższego dowodu ani trochę. *)

End reverse.