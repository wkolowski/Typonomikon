Inductive nel (A : Type) : Type :=
    | singl : A -> nel A
    | nel_cons : A -> nel A -> nel A.

Arguments singl [A] _.
Arguments nel_cons [A] _ _.

Notation "[ x ]" := (singl x).
Notation "h :: t" := (nel_cons h t).

Fixpoint foldr {A B : Type} (f : A -> B -> B) (b : B) (l : nel A) : B :=
match l with
    | [a] => f a b
    | h :: t => f h (foldr f b t)
end. 

Fixpoint len {A : Type} (l : nel A) : nat :=
match l with
    | [_] => 1
    | _ :: t => 1 + len t
end.

Fixpoint map {A B : Type} (f : A -> B) (l : nel A) : nel B :=
match l with
    | [h] => [f h]
    | h :: t => f h :: map f t
end.

Definition hd {A : Type} (l : nel A) : A :=
match l with
    | [h]    => h
    | h :: _ => h
end.

Fixpoint last {A} (l : nel A) : A :=
match l with
    | [h] => h
    | _ :: t => last t
end.

Definition tl {A : Type} (l : nel A) : option (nel A) :=
match l with
    | [_] => None
    | _ :: t => Some t
end.

Fixpoint init {A : Type} (l : nel A) : option (nel A) :=
match l with
    | [_] => None
    | h :: t =>
        match init t with
            | None => Some [h]
            | Some t' => Some (h :: t')
        end
end.

Theorem map_pres_len :
  forall {A B : Type} (f : A -> B) (l : nel A),
    len l = len (map f l).
Proof.
  induction l; unfold len in *; cbn; auto.
Qed.

Fixpoint app {A} (l1 l2 : nel A) : nel A :=
match l1 with
    | [h] => h :: l2
    | h :: t => h :: app t l2
end.

Notation "l1 ++ l2" := (app l1 l2).

Global Hint Unfold len : core.

Theorem app_length :
  forall {A : Type} (l1 l2 : nel A),
    len (l1 ++ l2) = len l1 + len l2.
Proof.
  induction l1; destruct l2; unfold len in *; cbn;
  try rewrite IHl1; auto.
Qed.

Fixpoint nth {A : Type} (n : nat) (l : nel A) : option A :=
match n with
    | 0 => Some (hd l)
    | S n' => match l with
        | [_] => None
        | _ :: t => nth n' t
    end
end.

Inductive Elem {A} : A -> nel A -> Prop :=
    | ElemZ :
        forall h : A, Elem h [h]
    | ElemS :
        forall (x h : A) (t : nel A),
          Elem x t -> Elem x (h :: t).

Fixpoint snoc {A : Type} (x : A) (l : nel A) : nel A :=
match l with
    | [h] => h :: [x]
    | h :: t => h :: snoc x t
end.

Fixpoint rev {A} (l : nel A) : nel A :=
match l with
    | [h] => [h]
    | h :: t => snoc h (rev t)
end.

Fixpoint zip {A B : Type} (l1 : nel A) (l2 : nel B) : nel (A * B) :=
match l1, l2 with
    | [a], [b] => singl (a, b)
    | [a], h' :: _ => singl (a, h')
    | h :: _, [b] => singl (h, b)
    | h :: t, h' :: t' => (h, h') :: zip t t'
end.

Fixpoint unzip {A B : Type} (l : nel (A * B)) : nel A * nel B :=
match l with
    | [(a, b)] => ([a], [b])
    | (a, b) :: t =>
        match unzip t with
            | (ta, tb) => (a :: ta, b :: tb)
        end
end.

Fixpoint zipWith {A B C : Type} (f : A -> B -> C) (la : nel A) (lb : nel B) : nel C :=
match la, lb with
    | [a], [b] => [f a b]
    | [a], b :: _ => [f a b]
    | a :: _, [b] => [f a b]
    | a :: ta, b :: tb => f a b :: zipWith f ta tb
end.


Fixpoint unzipWith {A B C : Type} (f : A -> B * C) (l : nel A) : nel B * nel C :=
match l with
    | [a] => let (b, c) := f a in ([b], [c])
    | h :: t =>
        match f h, unzipWith f t with
            | (a, b), (ta, tb) => (a :: ta, b :: tb)
        end
end.


(* TODO Fixpoint pmap {A B : Type} (f : A -> option B) (l : nel A) : list B :=
match l with
    | [h] =>
        match p h with
            | None => []
            | Some b => [b]
        end
    | h :: t =>
        match p h with
            | None => pmap f t
            | Some b => b :: pmap f t
        end
end.
*)

(** Rozkład na kawałki od początku i końca *)
Parameter tail' : forall A : Type, nel A -> list A.
Parameter uncons : forall A : Type, nel A -> option (A * nel A).

Parameter init' : forall A : Type, nel A -> list A.
Parameter unsnoc : forall A : Type, nel A -> option (A * nel A).




Fixpoint join {A : Type} (ll : nel (nel A)) : nel A :=
match ll with
    | [l] => l
    | h :: t => h ++ join t
end.

(* TODO: reszta rzeczy dla [nel]. *)
Parameter unzis : forall A B : Type, list (A + B) -> list A * list B.

(** Powtarzanie *)
Parameter replicate : forall A : Type, nat -> A -> nel A.
Parameter iterate : forall A : Type, (A -> A) -> nat -> A -> nel A.

(** Rozkład na kawałki *)
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