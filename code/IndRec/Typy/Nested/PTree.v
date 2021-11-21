Require Import Bool Recdef Equality FunctionalExtensionality.
Require Import List.
Import ListNotations.

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
    | Layer' : forall (x : A) (t : PTree (prod A A)),
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