Record rat : Set :=
{
    top : nat;
    bottom : nat;
    bottom_not_0 : bottom <> 0
}.

Class Equivalence {A : Type} (R : A -> A -> Prop) : Type :=
{
    reflexive : forall x : A, R x x;
    symmetry : forall x y : A, R x y -> R y x;
    transitive : forall x y z : A, R x y -> R y z -> R x z
}.

Instance Equivalence_eq (A : Type) : Equivalence (@eq A).
Proof.
  split.
    trivial.
    intros. rewrite H. trivial.
    intros. rewrite H, H0. trivial.
Qed.

Definition equiv_ex_rel (p1 p2 : nat * nat) : Prop :=
    fst p1 + snd p1 = fst p2 + snd p2.

Instance Equivalence_ex1 : Equivalence equiv_ex_rel.
Abort.

Definition equiv_kernel {A B : Type} (f : A -> B) : A -> A -> Prop :=
    fun x x' : A => f x = f x'.

Instance Equiv_kernel {A B : Type} {f : A -> B} : Equivalence (equiv_kernel f).
Abort.

Class Pos : Type :=
{
    carrier : Type;
    leq : carrier -> carrier -> Prop;
    pos_refl : forall x : carrier, leq x x;
    pos_sym : forall x y : carrier, leq y x;
    pos_trans : forall x y z : carrier, leq x y -> leq y z -> leq x z
}.

Check @carrier.

Coercion carrier : Pos >-> Sortclass.
(*Coercion leq : Pos >-> Funclass.*)

Theorem pos_leq_refl : forall (P : Pos) (x : P), leq x x.
Proof.
  intros. apply pos_refl.
Qed.

Class Lin : Type :=
{
    pos : Pos;
    total : forall x y : pos, leq x y \/ leq y x
}.

Coercion pos : Lin >-> Pos.