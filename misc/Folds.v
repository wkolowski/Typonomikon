Require Import List.
Import ListNotations.

Definition len {A : Type} (la : list A) : nat :=
    fold_right (fun _ n => S n) 0 la.

Print fold_right.
Print fold_left.

Eval simpl in len [1; 2; 3].

Goal forall (A : Type) (l1 l2 : list A),
    len (l1 ++ l2) = len l1 + len l2.
Proof.
  induction l1 as [| h t]; intros.
    simpl. trivial.
    simpl. rewrite IHt. trivial.
Defined.

Fixpoint range (n : nat) : list nat :=
    rev ((fix f (n : nat) : list nat :=
match n with
    | 0 => [0]
    | S n' => n :: f n'
end) n).

Definition fold {A B : Type} := @fold_right A B.

Eval simpl in fold plus 0 (range 10).

Definition l1 := [1; 2; 3].
Definition l2 := [4; 5; 6].

Eval compute in fold
    (fun h t => match t with
        | [] => l2
        | _ => h :: t
    end)
    l2 l1.

Print fold_right.
Print list_rec.

Eval compute in fold
    (fun h t => match t with
        | [] => [h]
        | _ => t ++ [h]
    end)
    [] (l1 ++ l2).

Eval compute in fold_left
    (*(fun t h => match t with
        | [] => [h]
        | _ => t ++ [h]
    end)*) (fun t h => h :: t)
    (l1 ++ l2) [].
 

Inductive BTree (A : Type) : Type :=
    | Empty : BTree A
    | Node : A -> BTree A -> BTree A -> BTree A.

Arguments Empty [A].
Arguments Node [A] _ _ _.

Fixpoint foldBT {A B : Type} (b : B) (f : A -> B -> B -> B)
    (btb : BTree A) : B :=
match btb with
    | Empty => b
    | Node v l r => f v (foldBT b f l) (foldBT b f r)
end.

Arguments Empty [A].
Arguments Node [A] _ _ _.

Definition wut := Node 42
    (Node 27
        (Node 8 Empty Empty)
        (Node 111 Empty Empty))
    (Node 1909
        Empty
        (Node 123 Empty Empty)).

Eval simpl in foldBT 0 (fun _ l r => S (l + r)) wut.

Eval simpl in foldBT [] (fun h l r => h :: l ++ r) wut.