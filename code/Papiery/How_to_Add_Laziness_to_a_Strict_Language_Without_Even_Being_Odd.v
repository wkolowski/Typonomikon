(** * How to Add Laziness to a Strict Languages Without Even Being Odd *)

(** ** 1 Introduction *)

(** ** 2 Odd and even, with ease and difficulty *)

Require Import CoqMTL.Control.Monad.Lazy.

(** *** 2.1 The odd style, with ease *)

(** This kind of streams is called odd because it contains odd number of
    constructors, where as constructors we count [Nil], [Cons] and delay. *)

Inductive OStream (A : Type) : Type :=
    | ONil : OStream A
    | OCons : A -> Lazy (OStream A) -> OStream A.

Arguments ONil {A}.
Arguments OCons {A} _ _.

Fixpoint omap {A B : Type} (f : A -> B) (os : OStream A) : OStream B :=
match os with
    | ONil => ONil
    | OCons h t => OCons (f h) (delay (omap f (force t)))
end.

Fixpoint ocountdown (n : nat) : OStream nat :=
match n with
    | 0 => OCons 0 (delay ONil)
    | S n' => OCons n (delay (ocountdown n'))
end.

Fixpoint ocutoff (n : nat) {A : Type} (os : OStream A) : OStream A :=
match n, os with
    | 0, _ => ONil
    | _, ONil => ONil
    | S n', OCons h t => OCons h (delay (ocutoff n' (force t)))
end.

(** *** 2.2 The even style, with difficulty *)

(*Inductive EStreamCell (A : Type) : Type :=
    | ENil : EStreamCell A
    | ECons : A -> EStream A -> EStreamCell A

with EStream (A : Type) : Type :=
    | mkEStream : Lazy (EStreamCell A) -> EStream A.

Arguments ENil {A}.
Arguments ECons {A} _ _.

Fixpoint emap {A B : Type} (f : A -> B) (es : EStream A) : EStream A :=
  delay (emap' f (force es))

with emap' {A B : Type} (f : A -> B) (esc : EStreamCell A) : EStreamCell A :=
match esc with
    | ENil => ENil
    | ECons h t => ECons (f h) (emap f t)
end.*)

(** This kind of streams is called "even" because all streams are made from
    an even number of constructors, where as constructors we count [ONil],
    [OCons] and [delay]. *)
Definition EStream (A : Type) : Type :=
  Lazy (OStream A).

Definition emap {A B : Type} (f : A -> B) (es : EStream A) : EStream B :=
  delay (omap f (force es)).

Definition ecountdown (n : nat) : EStream nat :=
  delay (ocountdown n).

Definition ecutoff (n : nat) {A : Type} (es : EStream A) : EStream A :=
  delay (ocutoff n (force es)).