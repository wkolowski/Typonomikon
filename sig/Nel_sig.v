Inductive nel (A : Type) : Type :=
    | singl : A -> nel A
    | nel_cons : A -> nel A -> nel A.

Arguments singl [A] _.
Arguments nel_cons [A] _ _.

Notation "[ x ]" := (singl x).
Notation "h :: t" := (nel_cons h t).

(** Rozkład na kawałki od początku *)
Parameter head : forall A : Type, nel A -> A.
Parameter tail : forall A : Type, nel A -> option (nel A).
Parameter tail' : forall A : Type, nel A -> list A.
Parameter uncons : forall A : Type, nel A -> option (A * nel A).

(** Proste obserwatory *)
Parameter isSingl : forall A : Type, nel A -> bool.
Parameter len : forall A : Type, nel A -> nat.

(** Proste funkcje *)
Parameter snoc : forall A : Type, nel A -> A -> nel A.
Parameter rev : forall A : Type, nel A -> nel A.
Parameter app : forall A : Type, nel A -> nel A -> nel A.

(** Rozkład na kawałki od końca *)
Parameter last : forall A : Type, nel A -> A.
Parameter init : forall A : Type, nel A -> option (nel A).
Parameter init' : forall A : Type, nel A -> list A.
Parameter unsnoc : forall A : Type, nel A -> option (A * nel A).

(** Operacje funktorowe, aplikatywne i monadyczne (+ zip) *)
Parameter map : forall A B : Type, (A -> B) -> nel A -> nel B.
Parameter pmap :
  forall A B : Type, (A -> option B) -> nel A -> nel B.

Parameter zip : forall A B : Type, list A -> list B -> list (A * B).
Parameter unzip : forall A B : Type, list (A * B) -> list A * list B.

Parameter zipWith :
  forall A B C : Type, (A -> B -> C) -> list A -> list B -> list C.
Parameter unzipWith :
  forall A B C : Type, (A -> B * C) -> list A -> list B * list C.

Parameter join : forall A : Type, list (list A) -> list A.

Parameter unzis : forall A B : Type, list (A + B) -> list A * list B.

(** Powtarzanie *)
Parameter replicate : forall A : Type, nat -> A -> nel A.
Parameter iterate : forall A : Type, (A -> A) -> nat -> A -> nel A.

(** Rozkład na kawałki *)
Parameter nth : forall A : Type, nel A -> nat -> option A.
Parameter take : forall A : Type, nat -> nel A -> nel A.
Parameter take' : forall A : Type, nat -> nel A -> list A.
Parameter drop : forall A : Type, nat -> nel A -> nel A.
Parameter drop' : forall A : Type, nat -> nel A -> list A.
Parameter splitAt :
  forall A : Type, nel A -> nat -> option (list A * A * list A).

(** Pochodne rozkładu na kawałki i jak powinno być*)
Parameter remove : forall A : Type, nat -> list A -> option (A * list A).
Parameter remove' : forall A : Type, nat -> list A -> option (list A).
Parameter remove'' : forall A : Type, nat -> list A -> list A.

(** Modyfikacje *)
Parameter replace : forall A : Type, nel A -> nat -> A -> option (nel A).
Parameter insert : forall A : Type, nel A -> nat -> A -> option (nel A).

(** Funkcje z predykatem boolowskim *)
Parameter any : forall A : Type, (A -> bool) -> nel A -> bool.
Parameter all : forall A : Type, (A -> bool) -> nel A -> bool.
Parameter count : forall A : Type, (A -> bool) -> nel A -> nat.
Parameter filter : forall A : Type, (A -> bool) -> nel A -> list A.
Parameter partition :
  forall A : Type, (A -> bool) -> nel A -> list A * list A.

(** Rozkład na kawałki według predykatu *)
Parameter find : forall A : Type, (A -> bool) -> nel A -> option A.
Parameter takeWhile : forall A : Type, (A -> bool) -> nel A -> list A.
Parameter dropWhile : forall A : Type, (A -> bool) -> nel A -> list A.
Parameter span :
  forall A : Type, (A -> bool) -> nel A -> option (list A * A * list A).

(** Pochodne rozkładu na kawałki według predykatu *)
Parameter removeFirst :
  forall A : Type, (A -> bool) -> nel A -> option (A * list A).
Parameter removeFirst' :
  forall A : Type, (A -> bool) -> nel A -> list A.

(** Rozkład na kawałki według predykatu od końca *)
Parameter findLast : forall A : Type, (A -> bool) -> nel A -> option A.
Parameter removeLast :
  forall A : Type, (A -> bool) -> nel A -> option (A * list A).
Parameter decomposeLast :
  forall A : Type, (A -> bool) -> nel A -> option (list A * A * list A).

(** Znajdowanie indeksów *)
Parameter findIndex :
  forall A : Type, (A -> bool) -> nel A -> option nat.

Parameter findIndices :
  forall A : Type, (A -> bool) -> nel A -> list nat.

(** Zwijanie i sumy częściowe *)
Parameter foldr : forall A B : Type, (A -> B -> B) -> B -> nel A -> B.
Parameter foldl : forall A B : Type, (A -> B -> A) -> A -> nel B -> A.

Parameter scanl : forall A B : Type, (A -> B -> A) -> A -> nel B -> nel A.
Parameter scanl1 : forall A : Type, (A -> A -> A) -> nel A -> nel A.

Parameter scanr : forall A B : Type, (A -> B -> B) -> B -> nel A -> nel B.
Parameter scanr1 : forall A : Type, (A -> A -> A) -> nel A -> nel A.

(** Bardziej skomplikowane funkcje *)
Parameter intersperse : forall A : Type, A -> nel A -> nel A.
Parameter extrasperse : forall A : Type, A -> nel A -> nel A.

Parameter splitBy :
  forall A : Type, (A -> bool) -> nel A -> list (list A).
Parameter groupBy :
  forall A : Type, (A -> A -> bool) -> nel A -> list (list A).

(** Predykat bycia elementem i jego pochodne *)
Parameter Elem : forall A : Type, A -> nel A -> Prop.
Parameter In : forall A : Type, A -> nel A -> Prop.

Parameter Dup : forall A : Type, nel A -> Prop.

Parameter Rep : forall A : Type, A -> nat -> nel A -> Prop.

Parameter Exists : forall A : Type, (A -> Prop) -> nel A -> Prop.
Parameter Forall : forall A : Type, (A -> Prop) -> nel A -> Prop.

Parameter AtLeast : forall A : Type, (A -> Prop) -> nat -> nel A -> Prop.
Parameter Exactly : forall A : Type, (A -> Prop) -> nat -> nel A -> Prop.
Parameter AtMost  : forall A : Type, (A -> Prop) -> nat -> nel A -> Prop.

(*
(** Listy jako termy *)
Parameter Subnel : forall A : Type, nel A -> nel A -> Prop.

(** Prefiksy i sufiksy *)
Parameter Prefix : forall A : Type, nel A -> nel A -> Prop.
Parameter Suffix : forall A : Type, nel A -> nel A -> Prop.

(** Listy jako ciągi, zbiory, multizbiory i cykle *)
Parameter Subseq : forall A : Type, nel A -> nel A -> Prop.

Parameter Incl : forall A : Type, list A -> list A -> Prop.
Parameter SetEquiv : forall A : Type, list A -> list A -> Prop.

Parameter Permutation : forall A : Type, list A -> list A -> Prop.
Parameter perm : forall (A : Type) (p : A -> bool), list A -> list A -> Prop.

Parameter Cycle: forall A : Type, list A -> list A -> Prop.

(** Palindromy *)
Parameter Palindrome : forall A : Type, list A -> Prop.
*)