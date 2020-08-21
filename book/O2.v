(** * O2: Podstawy analizy numerycznej *)

(** Podwaliny pod analizę numeryczną w Coqu, wzięte z
    https://www.brianheinold.net/numerical/
    An_Intuitive_Guide_to_Numerical_Methods_Heinold.pdf
*)

Require Import Floats.

Open Scope float.

Require Import List.
Import ListNotations.

Unset Guard Checking.

(** * 1 Introductory material *)

Fixpoint root2_aux (r x : float) (n : nat) : float :=
match n with
    | 0 => r
    | S n' => root2_aux ((r + x / r) / 2) x n'
end.

Compute map (root2_aux 1 1000) [0; 1; 2; 3; 4; 5; 6; 7]%nat.
Compute map (root2_aux 10 1000) [0; 1; 2; 3; 4; 5; 6; 7]%nat.

Definition root (x : float) : float := root2_aux (x / 10) x 50.

Compute map root [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 1e6; 1e12].

Compute 0.1 + 0.2.

Compute (1.000000000000001 - 1) * 100000000000000.

(** * 2.1 The bisection method *)

Fixpoint bisect (f : float -> float) (a b : float) (n : nat) : float :=
match n with
    | 0 => (a + b) / 2
    | S n' =>
        let m := (a + b) / 2 in
        if f a * f m < 0
        then bisect f a m n'
        else bisect f m b n'
end.

Definition f0 (x : float) : float := 1 - 2 * x - x * x * x * x * x.

Fixpoint fast_bisect
  (f : float -> float) (a b : float) (n : nat) : float :=
    let m := (a * f b - b * f a) / (f b - f a) in
match n with
    | 0 => m
    | S n' =>
        if f a * f m < 0
        then bisect f a m n'
        else bisect f m b n'
end.

Compute f0 0.
Compute f0 1.

Compute map (bisect f0 1 0) [0; 1; 2; 3; 4; 40]%nat.
Compute map f0 (map (bisect f0 1 0) [0; 1; 2; 3; 4; 40]%nat).
Compute map (fast_bisect f0 1 0) [0; 1; 2; 3; 4; 40]%nat.
Compute map f0 (map (fast_bisect f0 1 0) [0; 1; 2; 3; 4; 40]%nat).

(* ** 2.2 Fixed point iteration *)

Fixpoint iterf (f : float -> float) (x : float) (n : nat) : float :=
match n with
    | 0 => x
    | S n' => iterf f (f x) n'
end.

Definition f1 (x : float) : float := (1 - x * x * x * x * x) / 2.

Compute map (iterf f1 0) [0; 1; 2; 3; 4; 40]%nat.
Compute map f0 (map (iterf f1 0) [0; 1; 2; 3; 4; 40]%nat).

(** * Pochodna *)

Definition fdiff (h : float) (f : float -> float) (x : float) : float :=
  (f (x + h) - f x) / h.

Definition bdiff (h : float) (f : float -> float) (x : float) : float :=
  (f x - f (x - h)) / h.

Definition cdiff (h : float) (f : float -> float) (x : float) : float :=
  (f (x + h) - f (x - h)) / (2 * h).

Definition f2 (x : float) : float := x * x.

Definition hs : list float :=
  [1; 1e-1; 1e-2; 1e-3; 1e-4; 1e-5; 1e-6; 1e-7; 1e-8; 1e-9; 1e-10;
   1e-11; 1e-12; 1e-13; 1e-14; 1e-15; 1e-16].

Compute map (fun h => fdiff h f2 1) hs.
Compute map (fun h => bdiff h f2 1) hs.
Compute map (fun h => cdiff h f2 1) hs.

(** * 2.3 Newton's method *)

Fixpoint Newton
  (h : float) (f : float -> float) (x0 : float) (n : nat) : float :=
match n with
    | 0 => x0
    | S n' => Newton h f (x0 - f x0 / cdiff h f x0) n'
end.

Fixpoint Newton'
  (h : float) (f f' : float -> float) (x : float) (n : nat) : float :=
match n with
    | 0 => x
    | S n' => Newton' h f f' (x - f x / f' x) n'
end.

Compute map (Newton 1e-5 f2 2) [0; 1; 2; 3; 4; 5; 6; 7]%nat.

Definition f3 (x : float) : float := x * x - 2.

Compute map (Newton 1e-5 f3 2) [0; 1; 2; 3; 4; 5; 6; 7]%nat.
Compute map f3 (map (Newton 1e-5 f3 2) [0; 1; 2; 3; 4; 5; 6; 7]%nat).

Compute map (Newton' 1e-5 f3 (fun x => 2 * x) 2) [0; 1; 2; 3; 4; 5; 6; 7]%nat.
Compute map f3 (map (Newton 1e-5 f3 2) [0; 1; 2; 3; 4; 5; 6; 7]%nat).

(** * 2.4 Rates of convergence *)

Fixpoint Halley
  (h : float) (f : float -> float) (x : float) (n : nat) : float :=
match n with
    | 0 => x
    | S n' =>
        let f' := cdiff h f in
        let f'' := cdiff h f' in
        let x' := x - 2 * f x * f' x / (2 * f' x * f' x - f x * f'' x) in
          Halley h f x' n'
end.

Definition f4 (x : float) : float := x * x * x * x * x - 7 * x * x - 42.

Compute map (Newton 1e-5 f4 2) [0; 1; 2; 3; 4; 5; 6; 7]%nat.
Compute map f4 (map (Newton 1e-5 f4 2) [0; 1; 2; 3; 4; 5; 6; 7]%nat).

Compute map (Halley 1e-5 f4 2) [0; 1; 2; 3; 4; 5; 6; 7]%nat.
Compute map f4 (map (Halley 1e-5 f4 2) [0; 1; 2; 3; 4; 5; 6; 7]%nat).

(** * 2.5 Secant method *)

Fixpoint secant
  (h : float) (f : float -> float) (a b : float) (n : nat) : float :=
match n with
    | 0 => a
    | S n' => secant h f b (b - f b * (b - a) / (f b - f a)) n'
end.

Compute map (Newton 1e-5 f3 2) [0; 1; 2; 3; 4; 5; 6; 7]%nat.
Compute map f3 (map (Newton 1e-5 f3 2) [0; 1; 2; 3; 4; 5; 6; 7]%nat).
Compute map (secant 1e-5 f3 0 1) [0; 1; 2; 3; 4; 5; 6; 7]%nat.
Compute map f3 (map (secant 1e-5 f3 0 1) [0; 1; 2; 3; 4; 5; 6; 7]%nat).

(** * 2.7 Some more details on root-finding *)

Definition aitken (x : nat -> float) (n : nat) : float :=
  let a := x (1 + n)%nat - x n in
    x n - a * a / (x n - 2 * x (1 + n)%nat + x (2 + n)%nat).

Search float.

(*
Fixpoint es (x : float) (n : nat) : list float :=
match n with
    | 0 => []
    | S n' => x : es (exp x) n'
end.
*)