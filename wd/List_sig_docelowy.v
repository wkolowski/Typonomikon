Require Import Arith.

Inductive list (A : Type) : Type :=
    | nil : list A
    | cons : A -> list A -> list A.

Arguments nil [A].
Arguments cons [A] _ _.

Notation "[]" := nil.
Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(* Pomysły: collate (SML) *)

Parameter isEmpty : forall A : Type, list A -> bool.

Parameter length : forall A : Type, list A -> nat.

Parameter snoc : forall A : Type, A -> list A -> list A.

Parameter rev : forall A : Type, list A -> list A.

Parameter app : forall A : Type, list A -> list A -> list A.

Parameter replicate : forall A : Type, nat -> A -> list A.
(* TODO *)
Parameter iterate : forall A : Type, (A -> A) -> nat -> A -> list A.

Parameter head : forall A : Type, list A -> option A.
Parameter tail : forall A : Type, list A -> option (list A).
(* TODO *)
Parameter uncons : forall A : Type, list A -> option (A * list A).

Parameter last : forall A : Type, list A -> option A.
Parameter init : forall A : Type, list A -> option (list A).
(* TODO *)
Parameter unsnoc : forall A : Type, list A -> option (A * list A).

(* TODO *)
Parameter nth : forall A : Type, nat -> list A -> option A.
Parameter remove : forall A : Type, nat -> list A -> option (list A).
Parameter remove' : forall A : Type, nat -> list A -> list A.
Parameter nth_remove :
  forall A : Type, nat -> list A -> option (A * list A).

Parameter take : forall A : Type, nat -> list A -> list A.
Parameter drop : forall A : Type, nat -> list A -> list A.
Parameter takedrop : forall A : Type, nat -> list A -> list A * list A.
(* TODO: przenazwać [takedrop] na [splitAt]? *)

Parameter map : forall A B : Type, (A -> B) -> list A -> list B.
(* TODO *)
Parameter partialMap :
  forall A B : Type, (A -> option B) -> list A -> list B.

Parameter join : forall A : Type, list (list A) -> list A.

Parameter bind : forall A B : Type, (A -> list B) -> list A -> list B.

Parameter zip : forall A B : Type, list A -> list B -> list (A * B).

Parameter unzip : forall A B : Type, list (A * B) -> list A * list B.

Parameter zipWith :
  forall A B C : Type, (A -> B -> C) -> list A -> list B -> list C.

Parameter unzipWith :
  forall A B C : Type, (A -> B * C) -> list A -> list B * list C.

Parameter intersperse : forall A : Type, A -> list A -> list A.
Parameter splitBy :
  forall A : Type, (A -> bool) -> list A -> list (list A).

Parameter groupBy :
  forall A : Type, (A -> A -> bool) -> list A -> list (list A).

Parameter any : forall A : Type, (A -> bool) -> list A -> bool.
Parameter all : forall A : Type, (A -> bool) -> list A -> bool.

Parameter find : forall A : Type, (A -> bool) -> list A -> option A.
Parameter findLast : forall A : Type, (A -> bool) -> list A -> option A.

Parameter removeFirst :
  forall A : Type, (A -> bool) -> list A -> option (A * list A).
Parameter removeLast :
  forall A : Type, (A -> bool) -> list A -> option (A * list A).

Parameter findIndex :
  forall A : Type, (A -> bool) -> list A -> option nat.

Parameter count : forall A : Type, (A -> bool) -> list A -> nat.

Parameter filter : forall A : Type, (A -> bool) -> list A -> list A.
Parameter partition :
  forall A : Type, (A -> bool) -> list A -> list A * list A.

Parameter findIndices :
  forall A : Type, (A -> bool) -> list A -> list nat.

Parameter findIndices' :
  forall A : Type, (A -> bool) -> list A -> list nat.

Parameter takeWhile : forall A : Type, (A -> bool) -> list A -> list A.
Parameter dropWhile : forall A : Type, (A -> bool) -> list A -> list A.
Parameter takedropWhile :
  forall A : Type, (A -> bool) -> list A -> list A * list A.
(* TODO: przenazwać [takedropWhile] na [span]? *)
(* TODO: funkcja [break] jak w Haskellu, czyli span (not . p) *)

Parameter elem : forall A : Type, A -> list A -> Prop.
Parameter In : forall A : Type, A -> list A -> Prop.

Parameter NoDup : forall A : Type, list A -> Prop.
Parameter Dup : forall A : Type, list A -> Prop.

Parameter Rep : forall A : Type, A -> nat -> list A -> Prop.

Parameter Exists : forall A : Type, (A -> Prop) -> list A -> Prop.
Parameter Forall : forall A : Type, (A -> Prop) -> list A -> Prop.

Parameter AtLeast : forall A : Type, (A -> Prop) -> nat -> list A -> Prop.
Parameter Exactly : forall A : Type, (A -> Prop) -> nat -> list A -> Prop.
Parameter AtMost  : forall A : Type, (A -> Prop) -> nat -> list A -> Prop.

Parameter incl : forall A : Type, list A -> list A -> Prop.

Parameter sublist : forall A : Type, list A -> list A -> Prop.

Parameter Palindrome : forall A : Type, list A -> Prop.