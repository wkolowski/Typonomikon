Require Import BTree.
Require Import JMeq.

Inductive EnhBTree (A : Set) : nat -> Set :=
    | ENil : EnhBTree A 0
    | ENode : forall n m : nat,
        A -> EnhBTree A n -> EnhBTree A m -> EnhBTree A (n + m + 1).

Arguments ENil [A].
Arguments ENode [A] _ _ _ _ _.

Fixpoint emap {n : nat} {A B : Set} (f : A -> B) (et : EnhBTree A n)
    : EnhBTree B n := match et with
    | ENil => ENil
    | ENode m m' v l r => ENode m m' (f v) (emap f l) (emap f r)
end.

Fixpoint toBT {A : Set} {n : nat} (et : EnhBTree A n) : BTree A := match et with
    | ENil => empty
    | ENode m m' v l r => node v (toBT l) (toBT r)
end.
Coercion toBT : EnhBTree >-> BTree.

Theorem trolo : forall (A B : Set) (n : nat) (f : A -> B) (et : EnhBTree A n),
    toBT (emap f et) = map f (toBT et).
induction et; auto. simpl. f_equal. apply IHet1. apply IHet2.
Qed.

Instance Functor_EnhBTree (n : nat) : Functor (fun A : Set => EnhBTree A n).
split with (@emap n);
intros; rewrite fn_ext; induction a; simpl;
try rewrite IHa1, IHa2; trivial.
Qed.

Print fmap.

Inductive ETr (A : Set) {B : Set} (f : A -> B -> B -> B) : B -> Set :=
    | ENil' : forall b : B, ETr A f b
    | ENode' : forall (a : A) (b b' : B), A -> ETr A f b -> ETr A f b' ->
        ETr A f (f a b b').

Inductive AHTree : Set :=
    | any_height : forall n : nat, EnhBTree nat n -> AHTree.

Theorem any_height_inj2 : forall (n m : nat) (t1 : EnhBTree nat n)
    (t2 : EnhBTree nat m), any_height n t1 = any_height m t2 -> JMeq t1 t2.
intros. inversion H. trivial.
Qed.







