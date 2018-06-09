Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CoqBookPL.book.X3.

Parameter NoDup_snoc :
  forall (A : Type) (x : A) (l : list A),
    NoDup (snoc x l) <-> NoDup l /\ ~ elem x l.

(*
Parameter Rep_S_snoc :
  forall (A : Type) (x : A) (n : nat) (l : list A),
    Rep x n l -> Rep x (S n) (snoc x l).

Parameter Rep_snoc :
  forall (A : Type) (x y : A) (n : nat) (l : list A),
    Rep x n l -> x <> y -> Rep x n (snoc y l).
*)

Parameter Exactly_snoc :
  forall (A : Type) (P : A -> Prop) (n : nat) (x : A) (l : list A),
    Exactly P n l -> ~ P x -> Exactly P n (snoc x l).

Parameter Exactly_S_snoc :
  forall (A : Type) (P : A -> Prop) (n : nat) (x : A) (l : list A),
    Exactly P n l -> P x -> Exactly P (S n) (snoc x l).

Parameter AtMost_S_snoc :
  forall (A : Type) (P : A -> Prop) (n : nat) (x : A) (l : list A),
    AtMost P n l -> AtMost P (S n) (snoc x l).

Parameter AtMost_snoc :
  forall (A : Type) (P : A -> Prop) (n : nat) (x : A) (l : list A),
    AtMost P n l -> ~ P x -> AtMost P n (snoc x l).

Parameter incl_snoc :
  forall (A : Type) (x : A) (l : list A),
    incl l (snoc x l).

Parameter incl_snoc_snoc :
  forall (A : Type) (x : A) (l1 l2 : list A),
    incl l1 l2 -> incl (snoc x l1) (snoc x l2).

Parameter sublist_snoc :
  forall (A : Type) (x : A) (l : list A),
    sublist l (snoc x l).

Parameter sublist_snoc_snoc :
  forall (A : Type) (x : A) (l1 l2 : list A),
    sublist l1 l2 -> sublist (snoc x l1) (snoc x l2).

Parameter Palindrome_cons_snoc :
  forall (A : Type) (x : A) (l : list A),
    Palindrome l -> Palindrome (x :: snoc x l).