Inductive Law : Type :=
    | Id
    | Assoc
    | Comm
    | Idem.

Definition Laws : Type := Law -> bool.

Definition Magma (f : Law -> bool) : bool := true.

Definition Semigroup (f : Law -> bool) : bool :=
  f Assoc.

Definition Monoid (f : Law -> bool) : bool :=
  f Id && f Assoc.

Inductive Boom (A : Type) : (Law -> bool) -> Type :=
    | i  : forall f, A -> Boom A f
    | op : forall f, Boom A f -> Boom A f -> Boom A f
    | e  : forall f, f Id = true -> Boom A f.

