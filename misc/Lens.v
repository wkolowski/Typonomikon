Require Import String.
Require Import List.
Import ListNotations.

Record Point : Set :=
{
    x : nat;
    y : nat
}.

Record Atom : Set :=
{
    element : string;
    point : Point
}.

Record Molecule : Set :=
{
    atoms : list Atom
}.

Definition pt := {| x := 2; y := 2 |}.
Definition atomC := {| element := "C"; point := pt |}.
Definition atomO := {| element := "O"; point := {| x := 3; y := 6 |} |}.
Definition molecule := {| atoms := [atomC; atomO] |}.
Definition back_app {A B : Type} (x : A) (f : A -> B) : B := f x.
Notation "x $> f" := (back_app x f) (at level 40).

Check ((fun n : nat => n + 2) 5).
Check 5 $> fun n : nat => n + 2.

Check molecule $> atoms.
Check atomC $> point $> x.

Class Lens (A B : Type) : Type :=
{
    view : A -> B;
    over : (B -> B) -> (A -> A)
}.

Instance Lens_Point_nat : Lens Point nat :=
{
    view := x;
    over := fun (f : nat -> nat) (p : Point) =>
        {| x := f (p $> x); y := p $> y |}
}.

Eval compute in pt.
Eval compute in over (fun n => n + 1) pt.