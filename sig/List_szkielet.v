Require Import Arith.

Inductive list (A : Type) : Type :=
    | nil : list A
    | cons : A -> list A -> list A.

Arguments nil [A].
Arguments cons [A] _ _.

Notation "[]" := nil.
Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition isEmpty {A : Type} (l : list A) : bool :=
match l with
    | [] => true
    | _ => false
end.

Fixpoint length {A : Type} (l : list A) : nat :=
match l with
    | [] => 0
    | _ :: t => S (length t)
end.

Fixpoint app {A : Type} (l1 l2 : list A) : list A :=
match l1 with
    | [] => l2
    | h :: t => h :: app t l2
end.

Notation "l1 ++ l2" := (app l1 l2).

Fixpoint rev {A : Type} (l : list A) : list A :=
match l with
    | [] => []
    | h :: t => rev t ++ [h]
end.

Fixpoint map {A B : Type} (f : A -> B) (la : list A) : list B :=
match la with
    | [] => []
    | h :: t => f h :: map f t
end.

Fixpoint join {A : Type} (lla : list (list A)) : list A :=
match lla with
    | [] => []
    | h :: t => h ++ join t
end.

Fixpoint bind {A B : Type} (f : A -> list B) (l : list A) : list B :=
match l with
    | [] => []
    | h :: t => f h ++ bind f t
end.

Fixpoint replicate {A : Type} (n : nat) (x : A) : list A :=
match n with
    | 0 => []
    | S n' => x :: replicate n' x
end.

Fixpoint nth {A : Type} (n : nat) (l : list A) : option A :=
match n, l with
    | _, [] => None
    | 0, h :: t => Some h
    | S n', h :: t => nth n' t
end.

Fixpoint head {A : Type} (l : list A) : option A :=
match l with
    | [] => None
    | h :: _ => Some h
end.

Function last {A : Type} (l : list A) : option A :=
match l with
    | [] => None
    | [x] => Some x
    | h :: t => last t
end.

Fixpoint tail {A : Type} (l : list A) : option (list A) :=
match l with
    | [] => None
    | _ :: t => Some t
end.

Fixpoint init {A : Type} (l : list A) : option (list A) :=
match l with
    | [] => None
    | h :: t => match init t with
        | None => Some []
        | Some t' => Some (h :: t')
    end
end.

Fixpoint take {A : Type} (n : nat) (l : list A) : list A :=
match n, l with
    | 0, _ => []
    | _, [] => []
    | S n', h :: t => h :: take n' t
end.

Fixpoint drop {A : Type} (n : nat) (l : list A) : list A :=
match n, l with
    | 0, _ => l
    | _, [] => []
    | S n', h :: t => drop n' t
end.

Fixpoint takedrop {A : Type} (n : nat) (l : list A) : list A * list A :=
match n with
    | 0 => ([], l)
    | S n' =>
        match l with
            | [] => ([], [])
            | h :: t =>
                let '(l1, l2) := takedrop n' t
                in (h :: l1, l2)
        end
end.

Fixpoint filter {A : Type} (f : A -> bool) (l : list A) : list A :=
match l with
    | [] => []
    | h :: t => if f h then h :: filter f t else filter f t
end.

Fixpoint partition {A : Type} (p : A -> bool) (l : list A)
    : list A * list A :=
match l with
    | [] => ([], [])
    | h :: t => let (l1, l2) := partition p t in
        if p h then (h :: l1, l2) else (l1, h :: l2)
end.

Fixpoint takeWhile {A : Type} (p : A -> bool) (l : list A) : list A :=
match l with
    | [] => []
    | h :: t => if p h then h :: takeWhile p t else []
end.

Fixpoint dropWhile {A : Type} (p : A -> bool) (l : list A) : list A :=
match l with
    | [] => []
    | h :: t => if p h then dropWhile p t else l
end.

Fixpoint zip {A B : Type} (la : list A) (lb : list B) : list (A * B) :=
match la, lb with
    | [], _ => []
    | _, [] => []
    | ha :: ta, hb :: tb => (ha, hb) :: zip ta tb
end.

Fixpoint unzip {A B : Type} (l : list (A * B)) : list A * list B :=
match l with
    | [] => ([], [])
    | (ha, hb) :: t =>
        let (ta, tb) := unzip t in (ha :: ta, hb :: tb)
end.

Fixpoint zipWith {A B C : Type} (f : A -> B -> C)
  (la : list A) (lb : list B) : list C :=
match la, lb with
    | [], _ => []
    | _, [] => []
    | ha :: ta, hb :: tb => f ha hb :: zipWith f ta tb
end.

Fixpoint unzipWith
  {A B C : Type} (f : A -> B * C) (l : list A) : list B * list C :=
match l with
    | [] => ([], [])
    | h :: t =>
        let
          '(l1, l2) := unzipWith f t
        in let
          '(b, c) := f h
        in
          (b :: l1, c :: l2)
end.

Fixpoint intersperse {A : Type} (x : A) (l : list A) : list A :=
match l with
    | [] => []
    | [h] => [h]
    | h :: t => h :: x :: intersperse x t
end.

Fixpoint any {A : Type} (p : A -> bool) (l : list A) : bool :=
match l with
    | [] => false
    | h :: t => orb (p h) (any p t)
end.

Fixpoint all {A : Type} (p : A -> bool) (l : list A) : bool :=
match l with
    | [] => true
    | h :: t => andb (p h) (all p t)
end.

Function find {A : Type} (p : A -> bool) (l : list A) : option A :=
match l with
    | [] => None
    | h :: t => if p h then Some h else find p t
end.

Fixpoint findLast {A : Type} (p : A -> bool) (l : list A) : option A :=
match l with
    | [] => None
    | h :: t =>
        match findLast p t with
            | None => if p h then Some h else None
            | Some x => Some x
        end
end.

Function findIndex {A : Type} (p : A -> bool) (l : list A) : option nat :=
match l with
    | [] => None
    | h :: t =>
        if p h
        then Some 0
        else match findIndex p t with
            | None => None
            | Some n => Some (S n)
        end
end.

Fixpoint count {A : Type} (p : A -> bool) (l : list A) : nat :=
match l with
    | [] => 0
    | h :: t => if p h then S (count p t) else count p t
end.

Definition findIndices {A : Type} (p : A -> bool) (l : list A) : list nat :=
  (fix f (l : list A) (n : nat) : list nat :=
  match l with
      | [] => []
      | h :: t => if p h then n :: f t (S n) else f t (S n)
  end) l 0.

Fixpoint findIndices' {A : Type} (p : A -> bool) (l : list A) : list nat :=  
match l with
    | [] => []
    | h :: t =>
        if p h
        then 0 :: map S (findIndices' p t)
        else map S (findIndices' p t)
end.

Inductive elem {A : Type} : A -> list A -> Prop :=
    | elem_head : forall (x : A) (l : list A),
        elem x (x :: l)
    | elem_cons : forall (x h : A) (t : list A),
        elem x t -> elem x (h :: t).

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
match l with
    | [] => False
    | h :: t => x = h \/ In x t
end.

Inductive NoDup {A : Type} : list A -> Prop :=
    | NoDup_nil : NoDup []
    | NoDup_cons :
        forall (h : A) (t : list A),
          ~ elem h t -> NoDup t -> NoDup (h :: t).

Inductive Dup {A : Type} : list A -> Prop :=
    | Dup_elem :
        forall (h : A) (t : list A),
          elem h t -> Dup (h :: t)
    | Dup_tail :
        forall (h : A) (t : list A),
          Dup t -> Dup (h :: t).

Inductive Rep {A : Type} (x : A) : nat -> list A -> Prop :=
    | Rep_zero :
        forall l : list A, Rep x 0 l
    | Rep_cons_1 :
        forall (n : nat) (l : list A),
          Rep x n l -> Rep x (S n) (x :: l)
    | Rep_cons_2 :
        forall (n : nat) (l : list A) (y : A),
          Rep x n l -> Rep x n (y :: l).

Inductive Exists {A : Type} (P : A -> Prop) : list A -> Prop :=
    | Exists_head :
        forall (h : A) (t : list A), P h -> Exists P (h :: t)
    | Exists_tail :
        forall (h : A) (t : list A), Exists P t -> Exists P (h :: t).

Inductive Forall {A : Type} (P : A -> Prop) : list A -> Prop :=
    | Forall_nil : Forall P []
    | Forall_cons :
        forall (h : A) (t : list A), P h -> Forall P t -> Forall P (h :: t).

Inductive AtLeast {A : Type} (P : A -> Prop) : nat -> list A -> Prop :=
    | AL_0 :
        forall l : list A, AtLeast P 0 l
    | AL_S :
        forall (n : nat) (h : A) (t : list A),
          P h -> AtLeast P n t -> AtLeast P (S n) (h :: t)
    | AL_skip :
        forall (n : nat) (h : A) (t : list A),
          AtLeast P n t -> AtLeast P n (h :: t).

Inductive Exactly {A : Type} (P : A -> Prop) : nat -> list A -> Prop :=
    | Ex_0 : Exactly P 0 []
    | Ex_S :
        forall (n : nat) (h : A) (t : list A),
          P h -> Exactly P n t -> Exactly P (S n) (h :: t)
    | Ex_skip :
        forall (n : nat) (h : A) (t : list A),
          ~ P h -> Exactly P n t -> Exactly P n (h :: t).

Inductive AtMost  {A : Type} (P : A -> Prop) : nat -> list A -> Prop :=
    | AM_0 : forall n : nat, AtMost P n []
    | AM_S :
        forall (n : nat) (h : A) (t : list A),
          ~ P h -> AtMost P n t -> AtMost P n (h :: t)
    | AM_skip :
        forall (n : nat) (h : A) (t : list A),
          AtMost P n t -> AtMost P (S n) (h :: t).

Definition incl {A : Type} (l1 l2 : list A) : Prop :=
  forall x : A, elem x l1 -> elem x l2.

Inductive sublist {A : Type} : list A -> list A -> Prop :=
    | sublist_direct :
        forall (h : A) (t : list A), sublist t (h :: t)
    | sublist_trans :
        forall l1 l2 l3 : list A,
          sublist l1 l2 -> sublist l2 l3 -> sublist l1 l3.

Inductive Palindrome {A : Type} : list A -> Prop :=
    | Palindrome_nil : Palindrome []
    | Palindrome_singl :
        forall x : A, Palindrome [x]
    | Palindrome_1 :
        forall (x : A) (l : list A),
          Palindrome l -> Palindrome (x :: l ++ [x]).