Set Primitive Projections.

Require Import NArith.

CoInductive Div (A : Type) : Type :=
{
    call : A + Div A
}.

Fixpoint even (n : nat) : bool :=
match n with
    | 0 => true
    | 1 => false
    | S (S n') => even n'
end.

Require Import Div2.

(* The name is very unfortunate. *)
CoFixpoint collatz (n : nat) : Div unit :=
{|
    call :=
    match n with
        | 0 | 1 => inl tt
        | n' =>
            if even n'
            then inr (collatz (div2 n'))
            else inr (collatz (1 + 3 * n'))
    end
|}.

Print Div.

Fixpoint fuel (n : nat) {A : Type} (d : Div A) : option A :=
match n, d with
    | 0, _ => None
    | _, Build_Div _ (inl a) => Some a
    | S n', Build_Div _ (inr d') => fuel n' d'
end.

Compute fuel 5 (collatz 4).

CoInductive colist (A : Type) : Type :=
{
    uncons : unit + A * colist A
}.

Arguments uncons {A} _.

CoFixpoint collatz' (n : nat) : colist nat :=
match n with
    | 0 => {| uncons := inl tt |}
    | 1 => {| uncons := inr (1, {| uncons := inl tt |}) |}
    | n' =>
        if even n'
        then {| uncons := inr (n', collatz' (div2 n')) |}
        else {| uncons := inr (n', collatz' (1 + 3 * n')) |}
end.

Require Import List.
Import ListNotations.

Fixpoint take (n : nat) {A : Type} (l : colist A) : list A :=
match n, uncons l with
    | 0, _ => []
    | _, inl _ => []
    | S n', inr (h, t) => h :: take n' t
end.

Compute map (fun n : nat => take 200 (collatz' n)) [30; 31; 32; 33].
Compute take 150 (collatz' 12344).

