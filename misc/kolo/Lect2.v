(*Inductive bool : Set :=
    | true : bool
    | false : bool.

Inductive list (A : Type) : Type :=
    | nil : list A
    | cons : A -> list A -> list A.

Check nil.

Inductive vector (A : Type) : nat -> Type :=
    | vnil : vector A 0
    | vcons : forall n : nat,
        A -> vector A n -> vector A (S n).

Inductive eq {A : Type} (x : A) : A -> Prop :=
    | eq_refl : eq x x.

*)

Print bool.

Definition negb (b : bool) : bool :=
match b with
    | true => false
    | false => true
end.

Lemma negb_involutive :
  forall b : bool, negb (negb b) = b.
Proof.
  intro b; destruct b.
    cbn. exact (@eq_refl bool true).
    cbn. trivial.
Qed.

Goal (fun a : nat => a) = (fun b : nat => b).
Proof.
  trivial.
Qed.

Eval cbv delta in negb true.
Eval cbv delta beta in negb true.
Eval cbv delta beta iota in negb true.

Eval cbv zeta in let x := 5 in x.

Fail Fixpoint make_false (n : nat) : False :=
  make_false 42.