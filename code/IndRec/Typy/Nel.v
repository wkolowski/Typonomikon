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

Lemma map_pres_len :
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

Lemma app_length :
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

Fixpoint pmap {A B : Type} (f : A -> option B) (l : nel A) : list B :=
match l with
    | [h] =>
        match f h with
            | None => nil
            | Some b => cons b nil
        end
    | h :: t =>
        match f h with
            | None => pmap f t
            | Some b => cons b (pmap f t)
        end
end.

Fixpoint join {A : Type} (ll : nel (nel A)) : nel A :=
match ll with
    | [l] => l
    | h :: t => h ++ join t
end.

Fixpoint unzis {A B : Type} (l : nel (A + B)) : list A * list B :=
match l with
    | [inl a] => (cons a nil, nil)
    | [inr b] => (nil, cons b nil)
    | h :: t  =>
        let (la, lb) := unzis t in
          match h with
              | inl a => (cons a la, lb)
              | inr b => (la, cons b lb)
          end
end.

(** Powtarzanie *)
Fixpoint replicate (n : nat) {A : Type} (x : A) : nel A :=
match n with
    | 0    => [x]
    | S n' => x :: replicate n' x
end.

Fixpoint iterate (n : nat) {A : Type} (f : A -> A) (x : A) : nel A :=
match n with
    | 0    => [x]
    | S n' => x :: iterate n' f (f x)
end.

Fixpoint takeS (n : nat) {A : Type} (l : nel A) : nel A :=
match n, l with
    | _   , [h] => [h]
    | 0   , h :: _ => [h]
    | S n', h :: t => h :: takeS n' t
end.

Fixpoint take (n : nat) {A : Type} (l : nel A) : list A :=
match n, l with
    | 0   , _      => nil
    | S n', [h]    => cons h nil
    | S n', h :: t => cons h (take n' t)
end.

Fixpoint toList {A : Type} (l : nel A) : list A :=
match l with
    | [h]    => cons h nil
    | h :: t => cons h (toList t)
end.

Fixpoint drop (n : nat) {A : Type} (l : nel A) : list A :=
match n, l with
    | 0   , _      => toList l
    | S n', [_]    => nil
    | S n', h :: t => drop n' t
end.

Fixpoint any {A : Type} (p : A -> bool) (l : nel A) : bool :=
match l with
    | [h] => p h
    | h :: t => p h || any p t
end.

Fixpoint all {A : Type} (p : A -> bool) (l : nel A) : bool :=
match l with
    | [h]    => p h
    | h :: t => p h && all p t
end.

Fixpoint count {A : Type} (p : A -> bool) (l : nel A) : nat :=
match l with
    | [h]    => if p h then 1 else 0
    | h :: t => if p h then 1 + count p t else count p t
end.

Fixpoint filter {A : Type} (p : A -> bool) (l : nel A) : list A :=
match l with
    | [h]    => if p h then cons h nil else nil
    | h :: t => if p h then cons h (filter p t) else filter p t
end.

Fixpoint takeWhile {A : Type} (p : A -> bool) (l : nel A) : list A :=
match l with
    | [h]    => if p h then cons h nil else nil
    | h :: t => if p h then cons h (takeWhile p t) else nil
end.

Fixpoint dropWhile {A : Type} (p : A -> bool) (l : nel A) : list A :=
match l with
    | [h]    => if p h then nil else cons h nil
    | h :: t => if p h then dropWhile p t else toList t
end.

Fixpoint intersperse {A : Type} (x : A) (l : nel A) : nel A :=
match l with
    | [h]    => [h]
    | h :: t => h :: x :: intersperse x t
end.

Fixpoint extrasperse {A : Type} (x : A) (l : nel A) : nel A :=
match l with
    | [h] => x :: h :: [x]
    | h :: t => x :: h :: extrasperse x t
end.

(*
Compute intersperse 0 (1 :: 2 :: 3 :: 4 :: [5]).
Compute extrasperse 0 (1 :: 2 :: 3 :: 4 :: [5]).
*)

Inductive Exists {A : Type} (P : A -> Type) : nel A -> Type :=
    | ExZ  :
        forall h : A, P h -> Exists P [h]
    | ExZ' :
        forall (h : A) (t : nel A), P h -> Exists P (h :: t)
    | ExS  :
        forall (h : A) (t : nel A), Exists P t -> Exists P (h :: t).

Inductive Forall {A : Type} (P : A -> Type) : nel A -> Type :=
    | FZ :
        forall h : A, P h -> Forall P [h]
    | FS :
        forall (h : A) (t : nel A), P h -> Forall P t -> Forall P (h :: t).

Inductive DirectSubterm {A : Type} : nel A -> nel A -> Type :=
    | DS_cons  : forall (h : A) (t : nel A), DirectSubterm t (h :: t).