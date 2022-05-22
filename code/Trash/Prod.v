Require Import CoqMTL.Control.All.

Definition fmap_Prod
  {A B C : Type} (f : B -> C) (x : A * B) : A * C :=
match x with
    | pair a b => pair a (f b)
end.

Global Hint Unfold fmap_Prod : core.

#[refine]
Instance FunctorProd (A : Type) : Functor (prod A) :=
{
    fmap := @fmap_Prod A
}.
Proof. all: monad. Defined.

Theorem Prod_not_Applicative :
  (forall A : Type, Applicative (prod A)) -> False.
Proof.
  intro. destruct (X False). destruct (pure _ tt). assumption.
Qed.