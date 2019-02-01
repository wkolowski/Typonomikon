Class CombinatoryAlgebra : Type :=
{
    carrier : Type;
    op : carrier -> carrier -> carrier;
    S : carrier;
    K : carrier;
    I : carrier;
    S_eq : forall x y z, op (op (op S x) y) z = op (op x z) (op y z);
    K_eq : forall x y, op (op K x) y = x;
    I_eq : forall x, op I x = x;
}.

Notation "x * y" := (op x y) (at level 40, left associativity).

Goal
  forall A : CombinatoryAlgebra,
    S * S * S * S * S * S = S * S * (S * S * (S * S)).
Proof.
  intros. rewrite ?S_eq. reflexivity.
Qed.

Goal
  forall A : CombinatoryAlgebra,
    S * (S * S) * (S * S) * (S * S) * S * S = I.
Proof.
  intros. rewrite ?S_eq.
