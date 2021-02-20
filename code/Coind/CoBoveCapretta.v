(* TODO: rozszerzyć metodę Bove-Capretta na korekursję *)

CoInductive Stream (A : Type) : Type :=
{
    hd : A;
    tl : Stream A;
}.

Arguments hd {A} _.
Arguments tl {A} _.

Definition cons {A : Type} (h : A) (t : Stream A) : Stream A :=
{|
    hd := h;
    tl := t;
|}.

CoFixpoint zipWith
  {A B C : Type} (f : A -> B -> C) (sa : Stream A) (sb : Stream B) : Stream C :=
{|
    hd := f (hd sa) (hd sb);
    tl := zipWith f (tl sa) (tl sb);
|}.

Fail CoFixpoint fibs : Stream nat :=
{|
    hd := 0;
    tl := zipWith plus fibs (cons 1 fibs);
|}.

Set Implicit Arguments.

Inductive Call (C : Type) (F : Type -> Type) : Type :=
    | ht : C -> F C -> Call C F
    | zw : forall {A B : Type}, (A -> B -> C) -> F A -> F B -> Call C F. (* TODO: Call C F zamiast F A i F B *)

Arguments ht {C F} _ _.
Arguments zw {C F A B} _ _ _.

CoInductive ZipWith' (C : Type) : Type :=
{
    call : Call C ZipWith';
}.

Definition Cons {C : Type} (h : C) (t : ZipWith' C) : ZipWith' C :=
{|
    call := ht h t
|}.

Definition ZipWith
  {A B C : Type} (f : A -> B -> C)
  (zwa : ZipWith' A) (zwb : ZipWith' B) : ZipWith' C :=
{|
    call := zw f zwa zwb
|}.

CoFixpoint Fibs : ZipWith' nat :=
  Cons 0 (ZipWith plus Fibs (Cons 1 Fibs)).

(* Definition hdtl {C : Type} (c : Call C ZipWith') : C * ZipWith' C :=
match c with
    | ht h t => (h, t)
    | zw f s1 s2 =>
        match call s1, call s2 with
            | ht ha ta, ht hb tb => (f ha hb, {| call := 
 *)

Unset Guard Checking.
CoFixpoint fibs : Stream nat :=
{|
    hd := 0;
    tl := zipWith plus fibs (cons 1 fibs)
|}.

Require Import D5.

Fixpoint take {A : Type} (n : nat) (s : Stream A) : list A :=
match n with
    | 0 => []
    | S n' => hd s :: take n' (tl s)
end.

Compute take 20 fibs.