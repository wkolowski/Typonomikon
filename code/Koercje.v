Record Monoid : Type :=
{
    carrier : Type;
    op : carrier -> carrier -> carrier;
    id : carrier;
}.

Check carrier.
(* ===> carrier : Monoid -> Type *)

Fail Check forall (M : Monoid) (x : M), x = x.
(* ===> The command has indeed failed with message:
        In environment
        M : Monoid
        The term "M" has type "Monoid" which should be Set, Prop or Type. *)

Coercion carrier : Monoid >-> Sortclass.

Check forall (M : Monoid) (x : M), x = x.
(* ===> forall (M : Monoid) (x : M), x = x : Prop *)

(** Kiedy włączymy wyświetlanie koercji. *)

Check forall (M : Monoid) (x : M), x = x.
(* ===> forall (M : Monoid) (x : carrier M), x = x : Prop *)

Inductive Expr : Type :=
    | Lit : nat -> Expr
    | Plus : Expr -> Expr -> Expr.

Check Lit.
(* ===> Lit : nat -> Expr *)

Fail Check Plus 5 6.
(* ===> The command has indeed failed with message:
        The term "5" has type "nat" while it is expected to have type "Expr". *)

Coercion Lit : nat >-> Expr.

Check Plus 5 6.
(* ===> Plus 5 6 : Expr *)

(** Z włączonym wyświetlaniem koercji. *)

Check Plus 5 6.
(* ===> Plus (Lit 5) (Lit 6) : Expr *)

