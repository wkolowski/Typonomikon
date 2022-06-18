(** * P: Liczby [TODO] *)

(** * Liczby naturalne *)

(** ** Unarne *)

(** [nat] to jedyne normalne liczby, reszta to lipa.
    ~ parafraza z zapomniałem nazwiska, ale był Niemcem
    (albo Austryjakiem) *)

Print nat.
(* ===>
Inductive nat : Type :=
| O : nat
| S : nat -> nat.
*)

(** ** Dodatnie liczby naturalne, binarnie (TODO) *)

Inductive BinPos : Set :=
| H : BinPos
| O : BinPos -> BinPos
| I : BinPos -> BinPos.

(** [H] to binarne 1, [O k] to binarnie 2k, zaś [I k] to binarnie
    2k + 1. *)

Fixpoint to_nat (n : BinPos) : nat :=
match n with
| H => 1
| O n' => 2 * to_nat n'
| I n' => S (2 * to_nat n')
end.

Compute to_nat (O (O (O H))).

(** Liczby binarne można też zrobić inaczej, np. jako [list bool], ale
    wtedy reprezentacja nie jest unikalna. *)

(** * Liczby całkowite *)

(** ** Unarne *)

(** Jeżeli mamy liczby naturalne, to możemy zrobić liczby całkowite. *)

Module Z_unary.

Inductive Z : Type :=
| Z0 : Z
| Zpos : nat -> Z
| Zneg : nat -> Z.

End Z_unary.

(** ** Binarne *)

(** Mając dodatnie liczby binarne, możemy zrobić liczby całkowite za
    pomocą rozbicia na liczby ujemne, zero i dodatnie. *)

Module Z_binary.

Inductive Z : Set :=
| Z0 : Z
| Zpos : BinPos -> Z
| Zneg : BinPos -> Z.

End Z_binary.

(** ** Klasyczne *)

Module Z_classic.

Record Z : Type :=
{
    L : nat;
    R : nat;
}.

Definition Z_eq (k l : Z) : Prop :=
  L k + R l = R k + L l.

End Z_classic.

(** ** Klasyczne znormalizowane *)

Module Z_norm.

Record Z : Type := mkZ
{
    L : nat;
    R : nat;
}.

Fixpoint norm' (l r : nat) : nat * nat :=
match l, r with
| 0   , _    => (l, r)
| _   , 0    => (l, r)
| S l', S r' => norm' l' r'
end.

Definition norm (k : Z) : Z :=
  let (l, r) := norm' (L k) (R k) in mkZ l r.

Definition Z_eq (k l : Z) : Prop :=
  L k + R l = R k + L l.

End Z_norm.

(** ** HITowe *)

(** Jeżeli mamy wyższe typy induktywne, to można też spróbować definicji
    dość podobnej do [nat]. *)

Module Z_HIT.

Fail Inductive Z : Type :=
| zero : Z
| succ : Z -> Z
| pred : Z -> Z
| SP : forall z : Z, succ (pred z) = z
| PS : forall z : Z, pred (succ z) = z
| Z_isSet : forall (x y : Z) (p q : x = y), p = q.

End Z_HIT.

(** ** HITowe zasymulowane *)

Module Z_HIT_norm.

Inductive Z : Type :=
| zero : Z
| succ : Z -> Z
| pred : Z -> Z.

Fixpoint norm (k : Z) : Z :=
match k with
| zero    => zero
| succ k' =>
  match norm k' with
  | pred k'' => k''
  | k''      => succ k''
  end
| pred k' =>
  match norm k' with
  | succ k'' => k''
  | k''      => pred k''
  end
end.

Compute norm (succ (pred (succ zero))).

End Z_HIT_norm.

(** * Liczby wymierne (TODO) *)

(** ** Klasycznie *)

(** Liczby wymierne można zrobić naiwnie albo sprytnie (albo zastosować
    jakiś inny wariant), ale oba pomysły są dość głupie, bo w obu
    przypadkach potrzebne są setoidy. *)

Require Import ZArith.

Module Q_naive.

(** Bardzo naiwnie. *)

Record Q : Type :=
{
    numerator : Z;
    denominator : nat;
    _ : denominator <> 0;
}.

(** Warunek niezerowości można ulepszyć za pomocą sortu [SProp]. *)

Fail Definition Q_eq (q1 q2 : Q) : Prop :=
  numerator q1 * denominator q2 =
  numerator q2 * denominator q1.

End Q_naive.

Module Q_less_naive.

(** Sprytniej: mianownik interpretujemy jako liczbę dodatnią. *)

Record Q : Type :=
{
    numerator : Z;
    denominator : nat;
}.

Fail Definition Q_eq (q1 q2 : Q) : Prop :=
  numerator q1 * S (denominator q2) =
  numerator q2 * S (denominator q1).

End Q_less_naive.

(** ** HITowo *)

Module Q_HIT.

Fail Inductive Q : Type :=
| numden : Z -> nat -> Q
| path :
        forall (z1 z2 : Z) (n1 n2 : N),
          z1 * (S n2) = z2 * (S n1) -> numden z1 n1 = numden z2 n2.

End Q_HIT.

(** ** Induktywnie *)

(** Coś jak ułamki łańcuchowe:
    Yves Bertot,
    #<a class='link'
        href='https://www.researchgate.net/publication/220367791_Simple_canonical_representation_of_rational_numbers'>
    A simple canonical representation of rational numbers</a>#
*)

Module Q_Ind.

Inductive Q : Type :=
| One : Q
| N : Q -> Q
| D : Q -> Q.

End Q_Ind.

(** * Liczby rzeczywiste *)

(** Zbyt skomplikowane jak na jeden podrozdział - ludzie piszą o tym
    całe traktaty. *)

(** * Liczby porządkowe *)

(** ** Jakieś takie proste *)

Module Ord_simple.

Inductive Ord : Type :=
| ZZ : Ord
| SS : Ord -> Ord
| lim : (nat -> Ord) -> Ord.

End Ord_simple.

(** ** Skomplikowańsze *)

(** Indukcja-indukcja-rekursja wita nas: https://arxiv.org/pdf/1904.10759.pdf *)

Module Ord_IIR.

End Ord_IIR.

(** * Liczby nadrzeczywiste *)

(** Znów indukcja-indukcja wita. Patrz: HoTTBook, rozdział 11.6. *)

Module Sur.

End Sur.