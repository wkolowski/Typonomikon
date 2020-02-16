Module weak_apart.

Inductive unequal {A : Type} : list A -> list A -> Prop :=
    | nil_cons : forall h t, unequal nil (cons h t)
    | cons_nil : forall h t, unequal (cons h t) nil
    | cons_cons1 :
        forall h1 h2 t1 t2,
          h1 <> h2 -> unequal (cons h1 t1) (cons h2 t2)
    | cons_cons2 :
        forall h1 h2 t1 t2,
          unequal t1 t2 -> unequal (cons h1 t1) (cons h2 t2).

Fixpoint neq {A : Type} (l1 l2 : list A) : Prop :=
match l1, l2 with
    | nil, nil => False
    | nil, cons _ _ => True
    | cons _ _, nil => True
    | cons h1 t1, cons h2 t2 => h1 <> h2 \/ neq t1 t2
end.

Goal
  forall {A : Type} (l1 l2 : list A),
    unequal l1 l2 <-> neq l1 l2.
Proof.
  split.
    induction 1; cbn; firstorder.
    revert l2. induction l1 as [| h1 t1]; destruct l2 as [| h2 t2]; cbn.
      contradiction.
      1-2: constructor.
      destruct 1.
        constructor 3. assumption.
        constructor 4. apply IHt1. assumption.
Qed.

End weak_apart.

Module param_apart.

Inductive unequal
  {A : Type} (apart : A -> A -> Prop) : list A -> list A -> Prop :=
    | nil_cons : forall h t, unequal apart nil (cons h t)
    | cons_nil : forall h t, unequal apart (cons h t) nil
    | cons_cons1 :
        forall h1 h2 t1 t2,
          apart h1 h2 -> unequal apart (cons h1 t1) (cons h2 t2)
    | cons_cons2 :
        forall h1 h2 t1 t2,
          unequal apart t1 t2 -> unequal apart (cons h1 t1) (cons h2 t2).

Fixpoint neq
  {A : Type} (apart : A -> A -> Prop) (l1 l2 : list A) : Prop :=
match l1, l2 with
    | nil, nil => False
    | nil, cons _ _ => True
    | cons _ _, nil => True
    | cons h1 t1, cons h2 t2 => apart h1 h2 \/ neq apart t1 t2
end.

Goal
  forall {A : Type} (apart : A -> A -> Prop) (l1 l2 : list A),
    unequal apart l1 l2 <-> neq apart l1 l2.
Proof.
  split.
    induction 1; cbn; firstorder.
    revert l2. induction l1 as [| h1 t1]; destruct l2 as [| h2 t2]; cbn.
      contradiction.
      1-2: constructor.
      destruct 1.
        constructor 3. assumption.
        constructor 4. apply IHt1. assumption.
Qed.

End param_apart.

Require Import D5.

Fixpoint different {A : Type} (l1 l2 : list A) : Prop :=
match l1, l2 with
    | [], [] => False
    | [], _ => True
    | _, [] => True
    | h1 :: t1, h2 :: t2 => h1 <> h2 \/ different t1 t2
end.

Lemma different_spec :
  forall (A : Type) (l1 l2 : list A),
    l1 <> l2 <-> different l1 l2.
Proof.
  induction l1 as [| h1 t1]; cbn.
    destruct l2 as [| h2 t2]; cbn.
      tauto.
      firstorder congruence.
    destruct l2 as [| h2 t2]; cbn.
      firstorder congruence.
      split.
        Focus 2. destruct 1.
          congruence.
          destruct (IHt1 t2). firstorder congruence.
        intro. assert (~ (h1 = h2 /\ t1 = t2)).
          firstorder congruence.
Abort.