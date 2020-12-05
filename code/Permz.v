Require Import D5 D6.

(** * Permutacje przez wstawianie *)

Module Insert.

Inductive Insert {A : Type} (x : A) : list A -> list A -> Type :=
    | Insert_here :
        forall l : list A, Insert x l (x :: l)
    | Insert_there :
        forall (h : A) (t t' : list A), Insert x t t' -> Insert x (h :: t) (h :: t').

Inductive Perm {A : Type} : list A -> list A -> Prop :=
    | Perm_nil    : Perm [] []
    | Perm_Insert :
        forall (x : A) (l1 l1' l2 l2' : list A),
          Insert x l1 l1' -> Insert x l2 l2' -> Perm l1 l2 -> Perm l1' l2'.

Hint Constructors Insert Perm : core.

Lemma Perm_refl :
  forall {A : Type} (l : list A),
    Perm l l.
Proof.
  induction l as [| h t]; econstructor; eauto.
Qed.

Lemma Perm_Insert' :
  forall {A : Type} (x : A) (l1 l2 : list A),
    Insert x l1 l2 -> Perm (x :: l1) l2.
Proof.
  induction 1.
    apply Perm_refl.
    econstructor; eauto. apply Perm_refl.
Qed.

Lemma Perm_trans :
  forall {A : Type} {l1 l2 : list A},
    Perm l1 l2 -> forall l3 : list A, Perm l2 l3 -> Perm l1 l3.
Proof.
  intros until 2. revert l1 H.
  induction H0; intros.
    assumption.
    inv H.
      inv X.
      {
        apply Perm_Insert' in X.
        apply Perm_Insert' in X0.
        apply Perm_Insert' in X1.
        apply Perm_Insert' in X2.
Admitted.

Lemma Permutation_Perm :
  forall {A : Type} {l1 l2 : list A},
    Permutation l1 l2 -> Perm l1 l2.
Proof.
  induction 1.
    constructor.
    econstructor; eauto.
    econstructor; eauto. apply Perm_refl.
    eapply Perm_trans; eassumption.
Qed.

Lemma Permutation_Insert :
  forall {A : Type} (x : A) (l1 l2 : list A),
    Insert x l1 l2 -> Permutation (x :: l1) l2.
Proof.
  induction 1.
    reflexivity.
    econstructor; eauto.
Qed.

Lemma Perm_Permutation :
  forall {A : Type} {l1 l2 : list A},
    Perm l1 l2 -> Permutation l1 l2.
Proof.
  induction 1.
    reflexivity.
    {
      apply Permutation_Insert in X.
      apply Permutation_Insert in X0.
      rewrite <- X, <- X0.
      constructor.
      assumption.
    }
Qed.

End Insert.

Set Implicit Arguments.

Inductive BTree (A : Type) : Type :=
    | E : BTree A
    | N : A -> BTree A -> BTree A -> BTree A.

Inductive Position {A : Type} : BTree A -> Type :=
    | here :
        forall (v : A) (l r : BTree A),
          Position (N v l r)
    | left :
        forall (v : A) (l r : BTree A),
          Position l -> Position (N v l r)
    | right :
        forall (v : A) (l r : BTree A),
          Position r -> Position (N v l r).

Fixpoint get {A : Type} {t : BTree A} (p : Position t) : A :=
match p with
    | here  v _ _    => v
    | left  _ _ p' => get p'
    | right _ _ p' => get p'
end.

Fixpoint modify {A : Type} (f : A -> A) {t : BTree A} (p : Position t) : BTree A :=
match p with
    | here  v l r  => N (f v) l r
    | left  v r p' => N v (modify f p') r
    | right v l p' => N v l (modify f p')
end.

Record transposition {A : Type} (t1 t2 : BTree A) : Type :=
{
    p1 : Position t1;
    p2 : Position t1;
    transposition_spec :
      t2 = modify (fun _ => get p2) p1
}.
Print BTree.