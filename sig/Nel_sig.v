Inductive nel (A : Type) : Type :=
    | singl : A -> nel A
    | nel_cons : A -> nel A -> nel A.

Arguments singl [A] _.
Arguments nel_cons [A] _ _.

Notation "[ x ]" := (singl x).
Notation "h :: t" := (nel_cons h t).

Parameter head : forall A : Type, nel A -> A.
Parameter last : forall A : Type, nel A -> A.

Parameter len : forall A : Type, nel A -> nat.

Parameter snoc : forall A : Type, A -> nel A -> nel A.

Parameter rev : forall A : Type, nel A -> nel A.

Parameter app : forall A : Type, nel A -> nel A -> nel A.

Parameter replicate : forall A : Type, nat -> A -> nel A.
Parameter iterate : forall A : Type, nat -> A -> nel A.

Parameter tail : forall A : Type, nel A -> option (nel A).
Parameter tail' : forall A : Type, nel A -> list A.

Parameter init : forall A : Type, nel A -> option (nel A).
Parameter init' : forall A : Type, nel A -> list A.

Parameter take : forall A : Type, nat -> nel A -> nel A.
Parameter take' : forall A : Type, nat -> nel A -> list A.

Parameter drop : forall A : Type, nat -> nel A -> nel A.
Parameter drop' : forall A : Type, nat -> nel A -> list A.

Parameter takedrop : forall A : Type, nat -> nel A -> nel A * nel A.
Parameter takedrop' : forall A : Type, nat -> nel A -> list A * list A.

Parameter nth : forall A : Type, nat -> nel A -> option A.



Parameter any : forall A : Type, (A -> bool) -> nel A -> bool.
Parameter all : forall A : Type, (A -> bool) -> nel A -> bool.

Parameter find : forall A : Type, (A -> bool) -> nel A -> option A.
Parameter findLast : forall A : Type, (A -> bool) -> nel A -> option A.

Parameter findIndex :
  forall A : Type, (A -> bool) -> nel A -> option nat.

Parameter count : forall A : Type, (A -> bool) -> nel A -> nat.

Parameter filter : forall A : Type, (A -> bool) -> nel A -> list A.
Parameter partition :
  forall A : Type, (A -> bool) -> nel A -> list A * list A.

Parameter findIndices :
  forall A : Type, (A -> bool) -> nel A -> list nat.

Parameter takeWhile : forall A : Type, (A -> bool) -> nel A -> list A.
Parameter dropWhile : forall A : Type, (A -> bool) -> nel A -> list A.

Parameter findIndices' :
  forall A : Type, (A -> bool) -> nel A -> list nat.



Parameter map : forall A B : Type, (A -> B) -> nel A -> nel B.

Parameter join : forall A : Type, nel (nel A) -> nel A.

Parameter bind : forall A B : Type, (A -> nel B) -> nel A -> nel B.


Parameter zip : forall A B : Type, nel A -> nel B -> nel (A * B).

Parameter unzip : forall A B : Type, nel (A * B) -> nel A * nel B.

Parameter zipWith :
  forall A B C : Type, (A -> B -> C) -> nel A -> nel B -> nel C.

Parameter unzipWith :
  forall A B C : Type, (A -> B * C) -> nel A -> nel B * nel C.


Parameter intersperse : forall A : Type, A -> nel A -> nel A.


Parameter elem : forall A : Type, A -> nel A -> Prop.

Parameter In : forall A : Type, A -> nel A -> Prop.

Parameter NoDup : forall A : Type, nel A -> Prop.

Parameter Dup : forall A : Type, nel A -> Prop.

Parameter Rep : forall A : Type, A -> nat -> nel A -> Prop.

Parameter Exists : forall A : Type, (A -> Prop) -> nel A -> Prop.

Parameter Forall : forall A : Type, (A -> Prop) -> nel A -> Prop.

Parameter AtLeast : forall A : Type, (A -> Prop) -> nat -> nel A -> Prop.

Parameter Exactly : forall A : Type, (A -> Prop) -> nat -> nel A -> Prop.

Parameter AtMost  : forall A : Type, (A -> Prop) -> nat -> nel A -> Prop.

Parameter incl : forall A : Type, nel A -> nel A -> Prop.

Parameter subnel : forall A : Type, nel A -> nel A -> Prop.

Parameter Palindrome : forall A : Type, nel A -> Prop.