Require Import Arith.

Inductive list (A : Type) : Type :=
    | nil : list A
    | cons : A -> list A -> list A.

Arguments nil [A].
Arguments cons [A] _ _.

Notation "[]" := nil.
Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(** Proste obserwatory *)
Parameter isEmpty : forall A : Type, list A -> bool.
Parameter len : forall A : Type, list A -> nat.

(** Rozkład na kawałki od początku *)
Parameter head : forall A : Type, list A -> option A.
Parameter tail : forall A : Type, list A -> option (list A).
Parameter uncons : forall A : Type, list A -> option (A * list A).

(** Proste funkcje *)
Parameter snoc : forall A : Type, A -> list A -> list A.
Parameter rev : forall A : Type, list A -> list A.
Parameter app : forall A : Type, list A -> list A -> list A.
(* TODO *) Parameter revapp : forall A : Type, list A -> list A -> list A.

(** Rozkład na kawałki od końca *)
Parameter last : forall A : Type, list A -> option A.
Parameter init : forall A : Type, list A -> option (list A).
Parameter unsnoc : forall A : Type, list A -> option (A * list A).

(** Powtarzanie *)
Parameter replicate : forall A : Type, nat -> A -> list A.
Parameter iterate : forall A : Type, (A -> A) -> nat -> A -> list A.

(** Rozkład na kawałki *)
Parameter nth : forall A : Type, list A -> nat -> option A.
Parameter take : forall A : Type, list A -> nat -> list A.
Parameter drop : forall A : Type, list A -> nat -> list A.
Parameter splitAt :
  forall A : Type, list A -> nat -> option (list A * A * list A).

(** Pochodne rozkładu na kawałki i jak powinno być*)
Parameter remove : forall A : Type, nat -> list A -> option (A * list A).
Parameter remove' : forall A : Type, nat -> list A -> option (list A).
Parameter remove'' : forall A : Type, nat -> list A -> list A.

(** Modyfikacje *)
Parameter replace : forall A : Type, list A -> nat -> A -> option (list A).
Parameter insert : forall A : Type, list A -> nat -> A -> option (list A).
Parameter insert_orElse : forall A : Type, list A -> nat -> A -> list A.

(** Funkcje z predykatem boolowskim *)
Parameter any : forall A : Type, (A -> bool) -> list A -> bool.
Parameter all : forall A : Type, (A -> bool) -> list A -> bool.
Parameter count : forall A : Type, (A -> bool) -> list A -> nat.
Parameter filter : forall A : Type, (A -> bool) -> list A -> list A.
Parameter partition :
  forall A : Type, (A -> bool) -> list A -> list A * list A.

(** Rozkład na kawałki według predykatu *)
Parameter find : forall A : Type, (A -> bool) -> list A -> option A.
Parameter takeWhile : forall A : Type, (A -> bool) -> list A -> list A.
Parameter dropWhile : forall A : Type, (A -> bool) -> list A -> list A.
Parameter span :
  forall A : Type, (A -> bool) -> list A -> option (list A * A * list A).

(** Pochodne rozkładu na kawałki według predykatu *)
Parameter removeFirst :
  forall A : Type, (A -> bool) -> list A -> option (A * list A).
Parameter removeFirst' :
  forall A : Type, (A -> bool) -> list A -> list A.

(** Rozkład na kawałki według predykatu od końca *)
Parameter findLast : forall A : Type, (A -> bool) -> list A -> option A.
Parameter removeLast :
  forall A : Type, (A -> bool) -> list A -> option (A * list A).
Parameter decomposeLast :
  forall A : Type, (A -> bool) -> list A -> option (list A * A * list A).

(** Znajdowanie indeksów *)
Parameter findIndex :
  forall A : Type, (A -> bool) -> list A -> option nat.

Parameter findIndices :
  forall A : Type, (A -> bool) -> list A -> list nat.

(** Mapowanie i tympodobne *)
Parameter map : forall A B : Type, (A -> B) -> list A -> list B.

Parameter zip : forall A B : Type, list A -> list B -> list (A * B).

Parameter unzip : forall A B : Type, list (A * B) -> list A * list B.
Parameter unzis : forall A B : Type, list (A + B) -> list A * list B.

Parameter zipWith :
  forall A B C : Type, (A -> B -> C) -> list A -> list B -> list C.

Parameter unzipWith :
  forall A B C : Type, (A -> B * C) -> list A -> list B * list C.

(** Operacje aplikatywne i monadyczne *)
Parameter join : forall A : Type, list (list A) -> list A.
Parameter bind : forall A B : Type, (A -> list B) -> list A -> list B.
Parameter pmap :
  forall A B : Type, (A -> option B) -> list A -> list B.

(** Bardziej skomplikowane rzeczy *)
Parameter intersperse : forall A : Type, A -> list A -> list A.
Parameter splitBy :
  forall A : Type, (A -> bool) -> list A -> list (list A).
Parameter groupBy :
  forall A : Type, (A -> A -> bool) -> list A -> list (list A).

(** Zwijanie i sumy częściowe *)
Parameter foldr : forall A B : Type, (A -> B -> B) -> B -> list A -> B.
Parameter foldl : forall A B : Type, (A -> B -> A) -> A -> list B -> A.

Parameter scanl : forall A B : Type, (A -> B -> A) -> A -> list B -> list A.
Parameter scanl1 : forall A : Type, (A -> A -> A) -> list A -> list A.

Parameter scanr : forall A B : Type, (A -> B -> B) -> B -> list A -> list B.
Parameter scanr1 : forall A : Type, (A -> A -> A) -> list A -> list A.

(** Predykat bycia elementem i jego pochodne *)
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

(** Podlisty jako podtermy *)
Parameter sublist : forall A : Type, list A -> list A -> Prop.

(** Prefiksy i sufiksy *)
Parameter prefix : forall A : Type, list A -> list A -> Prop.
Parameter suffix : forall A : Type, list A -> list A -> Prop.

(** Palindromy *)
Parameter Palindrome : forall A : Type, list A -> Prop.

(** Listy jako zbiory, multizbiory i ciągi *)
Parameter incl : forall A : Type, list A -> list A -> Prop.
Parameter same_elements : forall A : Type, list A -> list A -> Prop.

Parameter Permutation : forall A : Type, list A -> list A -> Prop.
Parameter perm : forall (A : Type) (p : A -> bool), list A -> list A -> Prop.

Parameter subseq : forall A : Type, list A -> list A -> Prop.