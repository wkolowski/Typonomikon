(** Da się zrobić kombinator punktu stałego i zamknąć go w monadę/modalnośc
    tak, żeby sprzeczność nie wyciekła na zewnątrz i żeby wszystko ładnie się
    liczyło, jezeli wynik nie jest bottomem? TAK! *)

Module Type DIV.

Inductive Div (A : Type) : Type :=
    | div : A -> Div A.

Parameter efix :
  forall {A B : Type},
    ((A -> B) -> (A -> B)) -> (A -> Div B).


(* Definition figz {A : Type} (f : A -> A) : Div A :=
  efix (fun (g : A -> A) (x : A) => g (f x)).
 *)

End DIV.

Unset Guard Checking.
Fixpoint efix' {A B : Type} (f : (A -> B) -> (A -> B)) (x : A) {struct x} : B :=
  f (efix' f) x.
Set Guard Checking.

Require Import Arith.
Check Nat.compare.
Print comparison.

Compute efix'
  (fun euclid '(n, m) =>
    match Nat.compare n m with
        | Lt => euclid (n, m - n)
        | Eq => n
        | Gt => euclid (m, n - m)
    end)
  (360, 24).

Compute efix' (fun _ _ => 12) 123.

Inductive Div (A : Type) : Type :=
    | div : A -> Div A.

Arguments div {A} _.

Definition efix {A B : Type} (f : (A -> B) -> (A -> B)) : A -> Div B :=
  fun x : A => div (efix' f x).



