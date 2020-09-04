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

(** * HITowo *)

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
    A simple canonical representation of rational numbers,
    https://www.researchgate.net/publication/220367791_Simple_canonical_representation_of_rational_numbers
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

(** Indukcja-indukcja-rekursja wita nas:
    https://arxiv.org/pdf/1904.10759.pdf *)

Module Ord_IIR.

End Ord_IIR.

(** * Liczby nadrzeczywiste *)

(** Znów indukcja-indukcja wita. Patrz: HoTTBook, rozdział 11.6. *)

Module Sur.

End Sur.

(* begin hide *)

(*
TODO: uprzątnąć śmieci w postaci modułu [BinNat], któr zawiera jakąś
TODO kulawą implementację binarnych liczb naturalnych.
*)

Module BinNat.

Require Import List.
Import ListNotations.
Require Import Classes.SetoidClass.
Require Import Coq.Program.Wf.

Inductive D : Set :=
    | O : D
    | I : D.

Definition bin : Set := list D.

Inductive bin_equiv : bin -> bin -> Prop :=
    | equiv_refl : forall b : bin, bin_equiv b b
    | equiv_sym : forall b b' : bin, bin_equiv b b' -> bin_equiv b' b
    | equiv_trans : forall b1 b2 b3 : bin,
        bin_equiv b1 b2 -> bin_equiv b2 b3 -> bin_equiv b1 b3
    | equiv_nil : bin_equiv [O] []
    | equiv_leading_zeros : forall b b' : bin,
        bin_equiv b b' -> bin_equiv (O :: b) b'.

Hint Constructors bin_equiv.

#[refine]
Instance bin_setoid : Setoid bin :=
{
    equiv := bin_equiv
}.
Proof.
  split; red; eauto.
Qed.

Fixpoint normalize (b : bin) : bin :=
match b with
    | [] => []
    | O :: b' => normalize b'
    | _ => b
end.

Theorem normalize_spec :
  forall b : bin, bin_equiv b (normalize b).
Proof.
  induction b as [| d ds].
    cbn. eauto.
    destruct d; cbn.
      apply equiv_leading_zeros. assumption.
      constructor.
Qed.

Fixpoint bin_to_nat' (b : bin) : nat :=
match b with
    | [] => 0
    | O :: b' => 2 * bin_to_nat' b'
    | I :: b' => 1 + 2 * bin_to_nat' b'
end.

Definition bin_to_nat (b : bin) : nat :=
    bin_to_nat' (rev (normalize b)).

Eval compute in bin_to_nat [I; O; I; O; I; O].

Require Import Recdef.

Function divmod2 (n : nat) : nat * D :=
match n with
    | 0 => (0, O)
    | 1 => (0, I)
    | S (S n') => let (a, b) := divmod2 n' in (S a, b)
end.

Fixpoint nat_ind_2 (P : nat -> Prop) (H0 : P 0) (H1 : P 1)
    (H : forall n : nat, P n -> P (S (S n))) (n : nat) : P n :=
match n with
    | 0 => H0
    | 1 => H1
    | S (S n') => H n' (nat_ind_2 P H0 H1 H n')
end.

Ltac inv H := inversion H; subst; clear H.

Lemma divmod2_spec :
  forall (n m : nat) (d : D),
    divmod2 n = (m, d) -> m = 0 \/ m < n.
Proof.
  induction n using nat_ind_2; cbn; intros; inv H0.
    left. reflexivity.
    left. reflexivity.
    destruct (divmod2 n). inv H2. destruct (IHn _ _ eq_refl).
      right. rewrite H0. do 2 apply le_n_S. apply le_0_n.
      right. apply le_n_S. apply le_S. assumption.
Qed.

Require Import Recdef.

Function nat_to_bin' (n : nat) {measure id n} : bin :=
    let '(a, b) := divmod2 n in
    match a with
        | 0 => [b]
        | _ => b :: nat_to_bin' a
    end.
Proof.
  intros.
  destruct (divmod2_spec _ _ _ teq); subst.
    inv H0.
    unfold id. assumption.
Defined.

Definition nat_to_bin (n : nat) : bin := rev (nat_to_bin' n).

Goal
  forall n : nat, bin_to_nat (nat_to_bin n) = n.
Proof.
  unfold nat_to_bin. intro.
  functional induction (nat_to_bin' n). cbn.
    destruct b; cbn.
      functional inversion e. reflexivity.
      functional inversion e. reflexivity.
    cbn. unfold bin_to_nat in IHb. destruct a.
      contradiction.
      functional inversion e. subst.
Abort.

Compute bin_to_nat [I; O; I; O].
Compute bin_to_nat [I; O; O; O; I; I; I; I; O; I; I; O; I; I; I].

End BinNat.
(* end hide *)