Require Export ZArith.
Require Export Uint63.
Require Import List.
Import ListNotations.

Open Scope uint63.

Class Hashable (A : Type) : Type :=
{
  hash : A -> int;
}.

#[export] Instance Hashable_Empty_set : Hashable Empty_set :=
{
  hash e := match e with end;
}.

#[export] Instance Hashable_unit : Hashable unit :=
{
  hash _ := 147852369;
}.

#[export] Instance Hashable_bool : Hashable bool :=
{
  hash b := if b then 789654123 else 123654789;
}.

#[export] Instance Hashable_int : Hashable int :=
{
  hash i := i;
}.

#[export] Instance Hashable_nat : Hashable nat :=
{
  hash n := Uint63.of_Z (Z.of_nat n);
}.

#[export] Instance Hashable_sum
  {A B : Type} `{Hashable A} `{Hashable B} : Hashable (A + B) :=
{
  hash x :=
    match x with
    | inl a => add (mul 123456789 (hash a)) 987654321
    | inr b => add (mul 987654321 (hash b)) 123456789
    end;
}.

#[export] Instance Hashable_prod
  {A B : Type} `{Hashable A} `{Hashable B} : Hashable (A * B) :=
{
  hash '(a, b) :=
    let x := hash a in
    let y := hash b in
      div (add (mul x x) (add (mul 3 x) (add (mul 2 (mul x y)) (add y (mul y y))))) 2
}.

Fixpoint hash_list {A : Type} `{Hashable A} (l : list A) : int :=
match l with
| [] => hash tt
| h :: t => hash (hash h, hash_list t)
end.

#[export] Instance Hashable_list (A : Type) `{Hashable A} : Hashable (list A) :=
{
  hash := hash_list;
}.

Compute hash (inl false).
Compute hash (inl true).
Compute hash (inr false).
Compute hash (inr true).

Compute hash (inl (inl false)).
Compute hash (inl (inr false)).
Compute hash (inr (inl false)).
Compute hash (inr (inr false)).

Compute hash (true, false).
Compute hash (false, true).
Compute hash (true, true).
Compute hash (false, false).

Compute hash [true; false; true].