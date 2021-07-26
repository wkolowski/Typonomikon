(** Da się zrobić kombinator punktu stałego i zamknąć go w monadę/modalność
    tak, żeby sprzeczność nie wyciekła na zewnątrz i żeby wszystko ładnie się
    liczyło, jezeli wynik nie jest bottomem? TAK! *)

Unset Guard Checking.
Fixpoint efix' {A B : Type} (f : (A -> B) -> (A -> B)) (x : A) {struct x} : B :=
  f (efix' f) x.
Set Guard Checking.

Require Import Arith.

Inductive Div (A : Type) : Type :=
    | div : A -> Div A.

Arguments div {A} _.

Definition pure {A : Type} (x : A) : Div A := div x.

Definition bind {A B : Type} (x : Div A) (f : A -> Div B) : Div B :=
match x with
    | div a => f a
end.

Definition efix {A B : Type} (f : (A -> B) -> (A -> B)) : A -> Div B :=
  fun x : A => div (efix' f x).

Compute efix
  (fun euclid '(n, m) =>
    match Nat.compare n m with
        | Lt => euclid (n, m - n)
        | Eq => n
        | Gt => euclid (m, n - m)
    end)
  (360, 27).
