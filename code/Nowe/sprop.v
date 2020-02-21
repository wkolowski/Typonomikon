Set Allow StrictProp.

Inductive seq {A : Type} (x : A) : A -> SProp :=
    | srefl : seq x x.

Inductive sEmpty : SProp := .

Goal forall A : Type, sEmpty -> A.
Proof.
  destruct 1.
Qed.

Goal
  forall {A : Type} (P : A -> Type) (x y : A),
    seq x y -> P x -> P y.
Proof.
  intros A P x y Hs Hp.
Abort.