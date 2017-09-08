Require Import Bool.Bool.

Require Import MyOption.

Print list.

Inductive List (A : Type) : Type :=
    | Nil : List A
    | Cons : A -> List A -> List A.

Arguments Nil [A].
Arguments Cons [A] _ _.

Notation "[]" := Nil.
Notation "x :: y" := (Cons x y) (at level 60, right associativity).
Notation "[ x ; .. ; y ]" := (Cons x .. (Cons y Nil) ..).

Definition isNil {A : Type} (l : List A) : bool :=
match l with
    | [] => true
    | _ => false
end.

Definition isCons {A : Type} (l : List A) : bool :=
match l with
    | [] => false
    | _ => true
end.

Theorem isNil_or_isCons : forall (A : Type) (l : List A),
    isNil l || isCons l = true.
Proof.
  destruct l; simpl; trivial.
Qed.

Definition head {A : Type} (l : List A) : A? :=
match l with
    | [] => None
    | h :: _ => Some h
end.

Definition tail {A : Type} (l : List A) : (List A)? :=
match l with
    | [] => None
    | _ :: t => Some t
end.

Fixpoint zipWith {A B C : Type} (f : A -> B -> C) (la : List A) (lb : List B)
    : List C :=
match la, lb with
    | [], _ => []
    | _, [] => []
    | a :: la', b :: lb' => f a b :: zipWith f la' lb'
end.

Definition zip {A B C : Type} (la : List A) (lb : List B) : List (A * B) :=
    zipWith pair la lb.

Fixpoint unzip' {A B C : Type} (l : List (A * B * C))
    (acc : List A * List B * List C) : List A * List B * List C :=
match l with
    | Nil => acc
    | h :: t => match h, acc with
        | ((ha, hb), hc), ((la, lb), lc) =>
            unzip' t ((ha :: la, hb :: lb), hc :: lc)
    end
end.

Fixpoint take {A : Type} (n : nat) (l : List A) : List A :=
match n, l with
    | 0, _ => []
    | _, [] => []
    | S n', h :: t => h :: take n' t
end.

Eval compute in take 2 [1; 2; 3; 4; 5].

Fixpoint takeWhile {A : Type} (f : A -> bool) (l : List A) : List A :=
match l with
    | [] => []
    | h :: t => if f h then h :: takeWhile f t else [h]
end.

Theorem takeWhile_true : forall (A : Type) (l : List A),
    takeWhile (fun _ => true) l = l.
Proof.
  induction l as [| h t].
    simpl. trivial.
    simpl. f_equal. assumption.
Qed.

Inductive Elem {A : Type} (a : A) : List A -> Prop :=
    | Elem_here : forall t : List A, Elem a (a :: t)
    | Elem_later : forall (h : A) (t : List A),
        Elem a t -> Elem a (h :: t).

Fixpoint app {A : Type} (l1 l2 : List A) : List A :=
match l1, l2 with
    | [], _ => l2
    | h :: t, l2 => h :: app t l2
end.

Notation "l1 ++ l2" := (app l1 l2).

Theorem Elem_spec : forall (A : Type) (x : A) (l : List A),
    Elem x l <-> exists l1 l2 : List A, l = l1 ++ x :: l2.
Proof.
  split.
    induction 1.
      exists [], t. simpl. trivial.
      destruct IHElem as [l1 [l2 H']]. exists (h :: l1), l2.
        simpl. f_equal. assumption.
    induction l as [| h t]; intros.
      destruct H as [l1 [l2 H]]. destruct l1; inversion H.
      destruct H as [l1 [l2 H]]. destruct l1 as [| h' t'].
        simpl in H. inversion H. subst. constructor.
        simpl in H. inversion H. subst. constructor.
          apply IHt. exists t', l2. trivial.
Restart.
  split.
    induction 1.
      exists []; simpl; eauto.
      destruct IHElem as [l1 [l2 H']].
        exists (h :: l1), l2; subst; eauto.
    induction l as [| h t]; intros; destruct H as [l1 [l2 H]];
    destruct l1 as [| h' t']; simpl in H; inversion H; subst;
    constructor; eauto.
Qed.