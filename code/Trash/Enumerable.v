Require Import CoqMTL.Control.Applicative.
Require Import CoqMTL.Control.Monad.ListInst.
Require Import CoqMTL.Control.Monad.

Require Import List.
Import ListNotations.

(* Just for teh lulz. *)
Class Enumerable (A : Type) : Type :=
{
  enum : nat -> list A;
}.

Arguments enum _ {Enumerable} _.

#[export]
Instance Enumerable_Empty_set : Enumerable Empty_set :=
{
    enum n := []
}.

#[export]
Instance Enumerable_unit : Enumerable unit :=
{
    enum n :=
    match n with
    | 1 => [tt]
    | _ => []
    end
}.

#[export]
Instance Enumerable_bool : Enumerable bool :=
{
    enum n :=
    match n with
    | 1 => [false; true]
    | _ => []
    end
}.

#[export]
Instance Enumerable_prod
  (A B : Type) (instA : Enumerable A) (instB : Enumerable B)
  : Enumerable (A * B)%type :=
{
    enum n := liftA2 pair (enum A n) (enum B n)
}.

#[export]
Instance Enumerable_nat : Enumerable nat :=
{
    enum n := [n]
}.

#[export]
Instance Enumerable_list
  (A : Type) (inst : Enumerable A) : Enumerable (list A) :=
{
    enum :=
      fix f (n : nat) : list (list A) :=
      match n with
      | 0 => [[]]
      | S n' => liftA2 cons (enum A n) (f n')
      end
}.

#[export]
Instance Enumerable_sigma
  (A : Type) (P : A -> Type)
  (instA : Enumerable A) (instP : forall x : A, Enumerable (P x)) :
    Enumerable {x : A & P x} :=
{
    enum n := do
      x <- enum A n;
      p <- enum (P x) n;
      pure $ existT P x p
}.

Fixpoint cumulative (A : Type) {inst : Enumerable A} (n : nat) : list A :=
match n with
| 0 => enum A 0
| S n' => cumulative A n' ++ enum A n
end.

(*
Compute enum Empty_set 123.
Compute enum unit 11.
Compute cumulative unit 11.
Compute enum bool 5.
Compute cumulative bool 5.
Compute enum (bool * bool) 3.
Compute cumulative (bool * bool) 3.
Compute enum (list Empty_set) 0.
Compute enum (list unit) 20.
Compute enum (list bool) 4.
Compute cumulative nat 10.
Compute length (enum (list bool * list bool) 5).
Compute cumulative (list bool * list bool) 5.
*)