Require Import List.
Import ListNotations.

Inductive sorted {A : Type} (R : A -> A -> Prop) : list A -> Prop :=
    | nil_sorted : sorted R nil
    (* REST *).

SearchAbout le.

Check [2; 3; 1].

Inductive BTree (A : Type) : Type :=
    | Empty : BTree A
    | Node : A -> BTree A -> BTree A -> BTree A.

Arguments Empty [A].
Arguments Node [A] _ _ _.

(*Inductive symmetric {A : Type} : BTree A -> Prop :=
    | symmetric_Empty : symmetric Empty
    | symmetric_Leaf : forall x : A, symmetric (Node x Empty Empty)
    | symmetric_Same : forall (x y : A),
        symmetric (Node x (Node y Empty Empty)) (Node x (Node y Empty Empty))
    | symmetric_Node : forall (x : A) (l r : BTree A),*)

Fixpoint flip {A : Type} (b : BTree A) : BTree A :=
match b with
    | Empty => Empty
    | Node x l r => Node x (flip r) (flip l)
end.








































Eval compute in flip (Node 5 (Node 2 Empty Empty) (Node 7 Empty Empty)).

Inductive flipped {A : Type} : BTree A -> BTree A -> Prop :=
    | flipped_Empty : flipped Empty Empty
    | flipped_Node : forall (x : A) (l l' r r' : BTree A),
        flipped l l' -> flipped r r' -> flipped (Node x l r) (Node x r' l').

Inductive WeakFlipped {A : Type} : BTree A -> BTree A -> Prop :=
    | wFlippedEmpty : WeakFlipped Empty Empty
    | wFlippedNode : forall (v v' : A) (l l' r r' : BTree A),
        WeakFlipped l r' -> WeakFlipped r l' ->
        WeakFlipped (Node v l r) (Node v' l' r').

Definition symmetric {A : Type} (b : BTree A) : Prop := WeakFlipped b b.

Theorem flip_flipped : forall (A : Type) (b b' : BTree A),
    flip b = b' <-> flipped b b'.
Proof.
  split.
    generalize dependent b'. induction b as [| v l r].
      inversion 1. constructor.
      intros. rewrite <- H. simpl. constructor; auto.
    induction 1.
      simpl. trivial.
      subst. simpl. auto.
Defined.

Inductive reflect (P : Prop) : bool -> Set :=
    | ReflectT : P -> reflect P true
    | ReflectF : ~ P -> reflect P false.

Require Import Bool.Bool.

Fixpoint isFlipped {A : Type} (b b' : BTree A) : bool :=
match b, b' with
    | Empty, Empty => true
    | Node _ l r, Node _ l' r' =>
        andb (isFlipped l r') (isFlipped r l')
    | _, _ => false
end.

Theorem WeakFlipped_reflection : forall (A : Type) (b b' : BTree A),
    reflect (WeakFlipped b b') (isFlipped b b').
Proof.
  induction b as [| v l Hl r Hr]; destruct b' as [| v' l' r'];
  repeat constructor; try (inversion 1; fail); simpl.
  destruct (Hl r') as [H1 | H1], (Hr l') as [H2 | H2]; simpl;
  repeat constructor; try (intro; apply H1 || apply H2; inversion H; subst);
  assumption.
Qed.

