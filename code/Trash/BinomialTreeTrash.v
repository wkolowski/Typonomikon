(*Inductive BinomialTree (A : Type) : nat -> Type :=
    | leaf : A -> BinomialTree A 0
    | link :
        forall (rank : nat) (l r : BinomialTree A rank),
          BinomialTree A (S rank).

Module wut.

Inductive BinomialTree (A : Type) : nat -> Type :=
    | leaf : A -> BinomialTree A 0
    | forest : A -> forall {rank : nat}, BinomialForest A rank ->
        BinomialTree A (S rank)

with BinomialForest (A : Type) : nat -> Type :=
    | bfnil : BinomialForest A 0
    | bfcons : forall {r : nat},
        BinomialTree A (S r) -> BinomialForest A r ->
          BinomialForest A (S r).

Arguments leaf {A} _.
Arguments forest {A} _ {rank} _.
Arguments bfnil {A}.
Arguments bfcons {A r} _ _.

Inductive elem {A : Type} (x : A)
  : forall {r : nat}, BinomialTree A r -> Prop :=
    | elem_leaf : elem x (leaf x)
    | elem_forest_here :
        forall (r : nat) (f : BinomialForest A r),
          elem x (forest x f)
    | elem_forest_there :
        forall (y : A) (r : nat) (f : BinomialForest A r),
          elemForest x f -> elem x (forest y f)

with elemForest {A : Type} (x : A)
  : forall {r : nat}, BinomialForest A r -> Prop :=
    | elemForest_bfcons_tree :
        forall (r : nat) (t : BinomialTree A (S r)) (f : BinomialForest A r),
          elem x t -> elemForest x (bfcons t f)
    | elemForest_bfcons_forest :
        forall (r : nat) (t : BinomialTree A (S r)) (f : BinomialForest A r),
          elemForest x f -> elemForest x (bfcons t f).

Global Hint Constructors elem elemForest : core.

Fixpoint elem_dec
  {A : Ord} (x : A) {r : nat} (t : BinomialTree A r) :
    {elem x t} + {~ elem x t}

with elemForest_dec
  {A : Ord} (x : A) {r : nat} (f : BinomialForest A r) :
    {elemForest x f} + {~ elemForest x f}.
Proof.
  destruct t as [y | y r f].
    clear - x y. case_eq (x =? y); intros; trich.
      right. inv 1.
    case_eq (x =? y); intros.
      clear - x y H. trich.
      destruct (elemForest_dec A x r f).
        left. constructor. assumption.
        right. inv 1.
          trich.
          apply inj_pair2 in H4. subst. contradiction.
  destruct f.
    right. inv 1.
    destruct (elem_dec A x (S r) b).
      left. constructor. assumption.
      destruct (elemForest_dec A x r f).
        left. auto.
        right. inv 1; apply inj_pair2 in H1; apply inj_pair2 in H3; subst.
          contradiction.
          contradiction.
Defined.

End wut.

Module wut2.

Inductive BinomialTree (A : Type) : nat -> Type :=
    | node : A -> forall {r : nat}, BinomialForest A (pred r) ->
        BinomialTree A r

with BinomialForest (A : Type) : nat -> Type :=
    | bfnil : BinomialForest A 0
    | bfcons : forall {r : nat},
        BinomialTree A (S r) -> BinomialForest A r ->
          BinomialForest A (S r).

Arguments node {A} _ {r} _.
Arguments bfnil {A}.
Arguments bfcons {A r} _ _.

Inductive elem {A : Type} (x : A)
  : forall {r : nat}, BinomialTree A r -> Prop :=
    | elem_here :
        forall (r : nat) (f : BinomialForest A (pred r)),
          elem x (node x f)
    | elem_there :
        forall (y : A) (r : nat) (f : BinomialForest A (pred r)),
          elemForest x f -> elem x (node y f)

with elemForest {A : Type} (x : A)
  : forall {r : nat}, BinomialForest A r -> Prop :=
    | elemForest_bfcons_tree :
        forall (r : nat) (t : BinomialTree A (S r)) (f : BinomialForest A r),
          elem x t -> elemForest x (bfcons t f)
    | elemForest_bfcons_forest :
        forall (r : nat) (t : BinomialTree A (S r)) (f : BinomialForest A r),
          elemForest x f -> elemForest x (bfcons t f).

Global Hint Constructors elem elemForest : core.

Fixpoint elem_dec
  {A : Ord} (x : A) {r : nat} (t : BinomialTree A r) :
    {elem x t} + {~ elem x t}

with elemForest_dec
  {A : Ord} (x : A) {r : nat} (f : BinomialForest A r) :
    {elemForest x f} + {~ elemForest x f}.
Proof.
  destruct t as [y r f].
    case_eq (x =? y); intros.
      left. trich.
      destruct (elemForest_dec A x _ f).
        left. auto.
        right. inv 1.
          trich.
          apply inj_pair2 in H4. subst. contradiction.
  destruct f as [| r t f'].
    right. inv 1.
    destruct (elem_dec A x (S r) t).
      left. auto.
      destruct (elemForest_dec A x _ f').
        left. auto.
        right. inv 1; apply inj_pair2 in H1; apply inj_pair2 in H3;
          subst; contradiction.
Defined.

End wut2.

Module wut3.

Inductive BinomialTree (A : Type) : nat -> Type :=
    | node : A -> forall {r : nat}, BinomialForest A (pred r) ->
        BinomialTree A r

with BinomialForest (A : Type) : nat -> Type :=
    | bfnil : BinomialForest A 0
    | bfcons : forall {r : nat},
        BinomialTree A (S r) -> BinomialForest A r ->
          BinomialForest A (S r).

Arguments node {A} _ {r} _.
Arguments bfnil {A}.
Arguments bfcons {A r} _ _.

Inductive elem {A : Type} (x : A)
  : forall {r : nat}, BinomialTree A r -> Prop :=
    | elemC :
        forall (y : A) (r : nat) (f : BinomialForest A (pred r)),
          x = y \/ elemForest x f -> elem x (node y f)

with elemForest {A : Type} (x : A)
  : forall {r : nat}, BinomialForest A r -> Prop :=
    | elemForestC :
        forall (r : nat) (t : BinomialTree A (S r)) (f : BinomialForest A r),
          elem x t \/ elemForest x f -> elemForest x (bfcons t f).

Global Hint Constructors elem elemForest : core.

Fixpoint elem_dec
  {A : Ord} (x : A) {r : nat} (t : BinomialTree A r) :
    {elem x t} + {~ elem x t}

with elemForest_dec
  {A : Ord} (x : A) {r : nat} (f : BinomialForest A r) :
    {elemForest x f} + {~ elemForest x f}.
Proof.
  destruct t as [y r f].
    case_eq (x =? y); intros.
      left. trich.
      destruct (elemForest_dec A x _ f).
        left. auto.
        right. inv 1.
          trich.
          apply inj_pair2 in H4. inv H3.
  destruct f as [| r t f'].
    right. inv 1.
    destruct (elem_dec A x _ t).
      left. constructor. auto.
      destruct (elemForest_dec A x _ f').
        left. auto.
        right. inv 1; apply inj_pair2 in H1; apply inj_pair2 in H3;
          subst; inv H2.
Defined.

End wut3.

Module wut4.*)