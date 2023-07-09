(** * G2c: Typy induktywne zagnieżdżone parametrowo [TODO] *)

Require Import Bool Recdef Equality FunctionalExtensionality.
Require Import List.
Import ListNotations.

From Typonomikon Require Import D5.

(** * Parametry a indeksy (TODO) *)

(** * Rekursja polimorficzna *)

(** * Zupełne drzewa binarne (TODO) *)

Module Complete.

(* Pomysł na [Complete] wzięty
    #<a class='link' href='http://comonad.com/reader/wp-content/uploads/2010/04/Finger-Trees.pdf'>
    stąd</a>#. *)

Inductive Complete (A : Type) : Type :=
| Empty : Complete A
| Layer : A -> Complete (A * A) -> Complete A.

Arguments Empty {A}.
Arguments Layer {A} _ _.

Definition CompleteC (A : Type) :=
  forall
    (F : Type -> Type)
    (empty : forall A : Type, F A)
    (layer : forall A : Type, A -> F (prod A A) -> F A),
      F A.

Definition empty {A : Type} : CompleteC A :=
  fun F e l => e A.

Definition layer {A : Type} (x : A) (t : CompleteC (A * A)) : CompleteC A :=
  fun F e l => l A x (t F e l).

Fixpoint C2CC {A : Type} (t : Complete A) : CompleteC A :=
match t with
| Empty => empty
| Layer x t => layer x (C2CC t)
end.

Definition CC2C {A : Type} (t : CompleteC A) : Complete A :=
  t Complete (@Empty) (@Layer).

Lemma C2CC2C :
  forall {A : Type} (t : Complete A),
    CC2C (C2CC t) = t.
Proof.
  induction t as [| A x t'].
    compute. reflexivity.
    rewrite <- IHt' at 2.
      unfold CC2C. cbn. unfold layer. reflexivity.
Qed.

Function leftmost {A : Type} (t : Complete A) : option A :=
match t with
| Empty      => None
| Layer v t' =>
  match leftmost t' with
  | None   => Some v
  | Some (l, _) => Some l
  end
end.

Fixpoint rightmost {A : Type} (t : Complete A) : option A :=
match t with
| Empty      => None
| Layer v t' =>
  match rightmost t' with
  | None   => Some v
  | Some (_, r) => Some r
  end
end.

Fixpoint map {A B : Type} (f : A -> B) (t : Complete A) : Complete B :=
match t with
| Empty      => Empty
| Layer v t' => Layer (f v) (map (fun '(x, y) => (f x, f y)) t')
end.

Definition swap {A B : Type} (p : A * B) : B * A :=
match p with
| (x, y) => (y, x)
end.

Fixpoint mirror {A : Type} (t : Complete A) : Complete A :=
match t with
| Empty      => Empty
| Layer v t' => Layer v (map swap (mirror t'))
end.

Fixpoint nums (n : nat) : Complete nat :=
match n with
| 0    => Empty
| S n' => Layer n (map (fun x => (x, x)) (nums n'))
end.

Definition test : Complete nat :=
  Layer 0 (
  Layer (0, 1) (
  Layer (0, 1, (2, 3)) (
  Empty))).

Lemma map_id :
  forall {A : Type} (t : Complete A),
    map id t = t.
Proof.
  induction t; cbn; unfold id.
    reflexivity.
    rewrite <- IHt at 2. repeat f_equal.
      extensionality p. destruct p. reflexivity.
Qed.

Lemma map_map :
  forall {A B C : Type} (f : A -> B) (g : B -> C) (t : Complete A),
    map g (map f t) = map (fun x => g (f x)) t.
Proof.
  intros until t. revert B C f g.
  induction t; cbn; intros.
    reflexivity.
    rewrite IHt. repeat f_equal.
      extensionality x. destruct x. reflexivity.
Qed.

Lemma leftmost_map :
  forall {A B : Type} (f : A -> B) (t : Complete A),
    leftmost (map f t) =
      match leftmost t with
      | None   => None
      | Some a => Some (f a)
      end.
Proof.
  intros. revert B f.
  induction t; cbn; intros.
    reflexivity.
    rewrite IHt. destruct (leftmost t).
      destruct p. reflexivity.
      reflexivity.
Qed.

Lemma leftmost_mirror :
  forall {A : Type} (t : Complete A),
    leftmost (mirror t) = rightmost t.
Proof.
  induction t; cbn.
    reflexivity.
    rewrite leftmost_map, IHt.
      destruct (rightmost t) as [[] |]; cbn; reflexivity.
Qed.

Lemma map_mirror :
  forall {A B : Type} (f : A -> B) (t : Complete A),
    map f (mirror t) = mirror (map f t).
Proof.
  intros until t. revert B f.
  induction t; cbn; intros.
    reflexivity.
    rewrite <- IHt, !map_map. repeat f_equal.
      extensionality p. destruct p. cbn. reflexivity.
Qed.

Lemma mirror_mirror :
  forall {A : Type} (t : Complete A),
    mirror (mirror t) = t.
Proof.
  induction t; cbn.
    reflexivity.
    rewrite !map_mirror, map_map. rewrite <- IHt at 2.
      repeat f_equal. rewrite <- map_id. f_equal.
      extensionality p. destruct p. cbn. reflexivity.
Qed.

Fixpoint size {A : Type} (t : Complete A) : nat :=
match t with
| Empty => 0
| Layer v ts => 1 + size ts
end.

Fixpoint height {A : Type} (t : Complete A) : nat :=
match t with
| Empty => 0
| Layer _ ts => 1 + height ts
end.

Fixpoint flatten {A : Type} (l : list (A * A)) : list A :=
match l with
| [] => []
| (hl, hr) :: t => hl :: hr :: flatten t
end.

Fixpoint bfs {A : Type} (t : Complete A) : list A :=
match t with
| Empty => []
| Layer v ts => v :: flatten (bfs ts)
end.

Fixpoint complete {A : Type} (n : nat) (x : A) : Complete A :=
match n with
| 0 => Empty
| S n' => Layer x (complete n' (x, x))
end.

Fixpoint any {A : Type} (p : A -> bool) (t : Complete A) : bool :=
match t with
| Empty => false
| Layer v ts => p v || any (fun '(x, y) => p x || p y) ts
end.

Fixpoint all {A : Type} (p : A -> bool) (t : Complete A) : bool :=
match t with
| Empty => true
| Layer v ts => p v && all (fun '(x, y) => p x && p y) ts
end.

Fixpoint find {A : Type} (p : A -> bool) (t : Complete A) : option A :=
match t with
| Empty => None
| Layer v ts =>
  if p v
  then Some v
  else
    match find (fun '(x, y) => p x || p y) ts with
    | None => None
    | Some (x, y) => if p x then Some x else Some y
    end
end.

Fixpoint zipWith {A B C : Type} (f : A -> B -> C) (ta : Complete A) (tb : Complete B) : Complete C :=
match ta, tb with
| Empty, _ => Empty
| _, Empty => Empty
| Layer a ta', Layer b tb' => Layer (f a b) (zipWith (fun '(al, ar) '(bl, br) => (f al bl, f ar br)) ta' tb')
end.

Fixpoint left {A : Type} (t : Complete (A * A)) : Complete A :=
match t with
| Empty => Empty
| Layer (a, _) ts => Layer a (left ts)
end.

Fixpoint right {A : Type} (t : Complete (A * A)) : Complete A :=
match t with
| Empty => Empty
| Layer (_, a) ts => Layer a (right ts)
end.

(*Fixpoint count {A : Type} (p : A -> bool) (t : Complete A) : nat :=
match t with
| Empty => 0
| Layer v ts => (if p v then 1 else 0) + count (fun (x, y) => ts
end.*)

(* TODO

Parameter leaf : forall A : Type, A -> BTree A.

Parameter isEmpty : forall A : Type, BTree A -> bool.

Parameter root : forall A : Type, BTree A -> option A.

Parameter unN : forall A : Type, BTree A -> option (A * BTree A * BTree A).

Parameter inorder : forall A : Type, BTree A -> list A.
Parameter preorder : forall A : Type, BTree A -> list A.
Parameter postorder : forall A : Type, BTree A -> list A.

Parameter iterate : forall A : Type, (A -> A) -> nat -> A -> BTree A.

Parameter index : forall A : Type, list bool -> BTree A -> option A.
Parameter nth : forall A : Type, nat -> BTree A -> option A.

Parameter take : forall A : Type, nat -> BTree A -> BTree A.
Parameter drop : forall A : Type, nat -> BTree A -> list (BTree A).
Parameter takedrop :
  forall A : Type, nat -> BTree A -> BTree A * list (BTree A).

Parameter intersperse : forall A : Type, A -> BTree A -> BTree A.

Parameter insertAtLeaf :
  forall A : Type, list bool -> BTree A -> BTree A.

Parameter findIndex :
  forall A : Type, (A -> bool) -> BTree A -> option (list bool).

Parameter takeWhile : forall A : Type, (A -> bool) -> BTree A -> BTree A.

Parameter findIndices :
  forall A : Type, (A -> bool) -> BTree A -> list (list bool).

Parameter unzipWith :
 forall A B C : Type, (A -> B * C) -> BTree A -> BTree B * BTree C.
*)

Inductive Complete' {A : Type} (P : A -> Type) : Complete A -> Type :=
| Empty' : Complete' P Empty
| Layer' :
    forall (x : A) (t : Complete (prod A A)),
      P x -> Complete' (fun '(x, y) => prod (P x) (P y)) t -> Complete' P (Layer x t).

Fixpoint Complete_ind_deep
  (P : forall (A : Type) (Q : A -> Type), Complete A -> Type)
  (empty : forall (A : Type) (Q : A -> Type),
             P A Q Empty)
  (layer : forall (A : Type) (Q : A -> Type) (x : A) (t : Complete (A * A)),
             Q x -> P (prod A A) (fun '(x, y) => prod (Q x) (Q y)) t -> P A Q (Layer x t))
  {A : Type} (Q : A -> Type)
  {t : Complete A} (t' : Complete' Q t) {struct t'} : P A Q t.
Proof.
  destruct t' as [| x t Qx Ct].
    apply empty.
    apply layer.
      exact Qx.
      apply Complete_ind_deep; assumption.
Defined.

End Complete.

(** * [PTree], cokolwiek to jest (TODO) *)

Module PTree.

Inductive PTree (A : Type) : Type :=
| L : A -> PTree A
| N : PTree (A * A) -> PTree A.

Arguments L {A} _.
Arguments N {A} _.

Fixpoint map {A B : Type} (f : A -> B) (t : PTree A) : PTree B :=
match t with
| L x  => L (f x)
| N t' => N (map (fun '(x, y) => (f x, f y)) t')
end.

Definition swap {A B : Type} (p : A * B) : B * A :=
match p with
| (x, y) => (y, x)
end.

Fixpoint mirror {A : Type} (t : PTree A) : PTree A :=
match t with
| L x  => L x
| N t' => N (map swap (mirror t'))
end.

Function leftmost {A : Type} (t : PTree A) : option A :=
match t with
| L x  => Some x
| N t' =>
  match leftmost t' with
  | None        => None
  | Some (x, _) => Some x
  end
end.

Function rightmost {A : Type} (t : PTree A) : option A :=
match t with
| L x  => Some x
| N t' =>
  match rightmost t' with
  | None        => None
  | Some (_, x) => Some x
  end
end.

Fixpoint size {A : Type} (t : PTree A) : nat :=
match t with
| L x  => 0
| N t' => 1 + size t'
end.

Fixpoint height {A : Type} (t : PTree A) : nat :=
match t with
| L x => 0
| N t' => 1 + height t'
end.

Fixpoint flatten {A : Type} (l : list (A * A)) : list A :=
match l with
| [] => []
| (hl, hr) :: t => hl :: hr :: flatten t
end.

Fixpoint bfs {A : Type} (t : PTree A) : list A :=
match t with
| L x => [x]
| N t' => flatten (bfs t')
end.

Fixpoint complete {A : Type} (n : nat) (x : A) : PTree A :=
match n with
| 0 => L x
| S n' => N (complete n' (x, x))
end.

Fixpoint any {A : Type} (p : A -> bool) (t : PTree A) : bool :=
match t with
| L x  => p x
| N t' => any (fun '(x, y) => p x || p y) t'
end.

Fixpoint all {A : Type} (p : A -> bool) (t : PTree A) : bool :=
match t with
| L x  => p x
| N t' => all (fun '(x, y) => p x && p y) t'
end.

Fixpoint find {A : Type} (p : A -> bool) (t : PTree A) : option A :=
match t with
| L x  => if p x then Some x else None
| N t' =>
  match find (fun '(x, y) => p x || p y) t' with
  | None        => None
  | Some (x, y) => if p x then Some x else Some y
  end
end.

(*
Fixpoint zipWith {A B C : Type} (f : A -> B -> C) (ta : PTree A) (tb : PTree B) : PTree C :=
match ta, tb with
| L x, L y => L (f x y)
| _, L x => L x
| Layer a ta', Layer b tb' => Layer (f a b) (zipWith (fun '(al, ar) '(bl, br) => (f al bl, f ar br)) ta' tb')
end.
*)

Fixpoint left {A : Type} (t : PTree (A * A)) : PTree A :=
match t with
| L (x, _) => L x
| N t'     => N (left t')
end.

Fixpoint right {A : Type} (t : PTree (A * A)) : PTree A :=
match t with
| L (x, _) => L x
| N t'     => N (right t')
end.

Fixpoint count {A : Type} (p : A -> nat) (t : PTree A) : nat :=
match t with
| L x  => p x
| N t' => count (fun '(x, y) => p x + p y) t'
end.

(* TODO

Parameter leaf : forall A : Type, A -> BTree A.

Parameter isL x : forall A : Type, BTree A -> bool.

Parameter root : forall A : Type, BTree A -> option A.

Parameter unN : forall A : Type, BTree A -> option (A * BTree A * BTree A).

Parameter inorder : forall A : Type, BTree A -> list A.
Parameter preorder : forall A : Type, BTree A -> list A.
Parameter postorder : forall A : Type, BTree A -> list A.

Parameter iterate : forall A : Type, (A -> A) -> nat -> A -> BTree A.

Parameter index : forall A : Type, list bool -> BTree A -> option A.
Parameter nth : forall A : Type, nat -> BTree A -> option A.

Parameter take : forall A : Type, nat -> BTree A -> BTree A.
Parameter drop : forall A : Type, nat -> BTree A -> list (BTree A).
Parameter takedrop :
  forall A : Type, nat -> BTree A -> BTree A * list (BTree A).

Parameter intersperse : forall A : Type, A -> BTree A -> BTree A.

Parameter insertAtLeaf :
  forall A : Type, list bool -> BTree A -> BTree A.

Parameter findIndex :
  forall A : Type, (A -> bool) -> BTree A -> option (list bool).

Parameter takeWhile : forall A : Type, (A -> bool) -> BTree A -> BTree A.

Parameter findIndices :
  forall A : Type, (A -> bool) -> BTree A -> list (list bool).

Parameter unzipWith :
 forall A B C : Type, (A -> B * C) -> BTree A -> BTree B * BTree C.
*)

Lemma map_id :
  forall {A : Type} (t : PTree A),
    map id t = t.
Proof.
  induction t; cbn; unfold id.
    reflexivity.
    rewrite <- IHt at 2. repeat f_equal.
      extensionality p. destruct p. reflexivity.
Qed.

Lemma map_map :
  forall {A B C : Type} (f : A -> B) (g : B -> C) (t : PTree A),
    map g (map f t) = map (fun x => g (f x)) t.
Proof.
  intros until t. revert B C f g.
  induction t; cbn; intros.
    reflexivity.
    rewrite IHt. repeat f_equal.
      extensionality x. destruct x. reflexivity.
Qed.

Lemma leftmost_map :
  forall {A B : Type} (f : A -> B) (t : PTree A),
    leftmost (map f t) =
      match leftmost t with
      | None   => None
      | Some a => Some (f a)
      end.
Proof.
  intros. revert B f.
  induction t; cbn; intros.
    reflexivity.
    rewrite IHt. destruct (leftmost t).
      destruct p. reflexivity.
      reflexivity.
Qed.

Lemma leftmost_mirror :
  forall {A : Type} (t : PTree A),
    leftmost (mirror t) = rightmost t.
Proof.
  induction t; cbn.
    reflexivity.
    rewrite leftmost_map, IHt.
      destruct (rightmost t) as [[] |]; cbn; reflexivity.
Qed.

Lemma map_mirror :
  forall {A B : Type} (f : A -> B) (t : PTree A),
    map f (mirror t) = mirror (map f t).
Proof.
  intros until t. revert B f.
  induction t; cbn; intros.
    reflexivity.
    rewrite <- IHt, !map_map. repeat f_equal.
      extensionality p. destruct p. cbn. reflexivity.
Qed.

Lemma mirror_mirror :
  forall {A : Type} (t : PTree A),
    mirror (mirror t) = t.
Proof.
  induction t; cbn.
    reflexivity.
    rewrite !map_mirror, map_map. rewrite <- IHt at 2.
      repeat f_equal. rewrite <- map_id. f_equal.
      extensionality p. destruct p. cbn. reflexivity.
Qed.

(*
Inductive PTree' {A : Type} (P : A -> Type) : PTree A -> Type :=
| L x' : PTree' P L x
| Layer' :
    forall (x : A) (t : PTree (prod A A)),
      P x -> PTree' (fun '(x, y) => prod (P x) (P y)) t -> PTree' P (Layer x t).

Fixpoint PTree_ind_deep
  (P : forall (A : Type) (Q : A -> Type), PTree A -> Type)
  (empty : forall (A : Type) (Q : A -> Type),
             P A Q L x)
  (layer : forall (A : Type) (Q : A -> Type) (x : A) (t : PTree (A * A)),
             Q x -> P (prod A A) (fun '(x, y) => prod (Q x) (Q y)) t -> P A Q (Layer x t))
  {A : Type} (Q : A -> Type)
  {t : PTree A} (t' : PTree' Q t) {struct t'} : P A Q t.
Proof.
  destruct t' as [| x t Qx Ct].
    apply empty.
    apply layer.
      exact Qx.
      apply PTree_ind_deep; assumption.
Defined.
*)

End PTree.

(** * Zagnieżdżone listy (TODO) *)

Module Nested.

Inductive Nested (A : Type) : Type :=
| Epsilon
| Cons (h : A) (t : Nested (list A)).

Arguments Epsilon {A}.
Arguments Cons    {A} _ _.

Inductive Nested' : Type -> Type :=
| Epsilon' : forall A : Type, Nested' A
| Cons' : forall A : Type, A -> Nested' (list A) -> Nested' A.

Fixpoint len {A : Type} (l : Nested A) : nat :=
match l with
| Epsilon => 0
| Cons _ t => 1 + len t
end.

Fixpoint size {A : Type} (l : Nested A) : nat :=
match l with
| Epsilon => 0
| Cons _ Epsilon => 1
| Cons _ (Cons h t) => length h + size t
end.

Lemma wut :
  forall {A : Type} (l : Nested A),
    len l <= size l.
Proof.
  induction l as [| h t]; cbn.
  - easy.
  - destruct l as [| h' t']; cbn.
    + easy.
    + cbn in IHl.
Abort.

End Nested.

(** * Zagnieżdżone listy niepuste (TODO) *)

Module Nested2.

Inductive Nested (A : Type) : Type :=
| Singl : A -> Nested A
| Nestd : Nested (list A) -> Nested A.

End Nested2.

(** * Swap-drzewka (TODO) *)

Inductive SwapTree (A B : Type) : Type :=
| E : SwapTree A B
| N : A -> SwapTree B A -> SwapTree B A -> SwapTree A B.