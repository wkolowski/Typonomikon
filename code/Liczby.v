(* [nat] to jedyne normalne liczby, reszta to lipa.
    ~ parafraza z zapomniałem nazwiska, ale był Niemcem (albo Austryjakiem)
*)
(*
Inductive nat : Type :=
    | O : nat
    | S : nat -> nat.
*)

(** Można je też zrobić inaczej, np. jako [list bool], ale wtedy
    reprezentacja nie jest unikalna. *)

(* Jak zrobić inne rodzaje liczb? *)

(** Dodatnie liczby binarne.
    H to 1, O k to 2k, I k to 2k + 1. *)

Inductive BinPos : Set :=
    | H : BinPos
    | O : BinPos -> BinPos
    | I : BinPos -> BinPos.

Fixpoint to_nat (n : BinPos) : nat :=
match n with
    | H => 1
    | O n' => 2 * to_nat n'
    | I n' => S (2 * to_nat n')
end.

Compute to_nat (O (O (O H))).

(** Mając jakieś liczby dodatnie, możemy zrobić liczby całkowite za pomocą
    rozbicia na liczby ujemne, zero i dodatnie. *)
Inductive Z : Set :=
    | Z0 : Z
    | Zpos : BinPos -> Z
    | Zneg : BinPos -> Z.

(** Inaczej liczby całkowite można zrobić za pomocą liczb naturalnych, o
    ile mamy wyższe typy induktywne. *)

(*
Inductive Z : Type :=
    | negZ : nat -> Z
    | posZ : nat -> Z
    | coh : negZ 0 = posZ 0.
*)

(** Najbardziej ludzka HITowa definicja wygląda tak: *)

(*
Inductive Z : Type :=
    | zero : Z
    | succ : Z -> Z
    | pred : Z -> Z
    | SP : forall z : Z, succ (pred z) = z
    | PS : forall z : Z, pred (succ z) = z
    | Z_isSet : forall (x y : Z) (p q : x = y), p = q.
*)

(** Liczby wymierne można zrobić naiwnie albo sprytnie, ale oba pomysły są
    głupie. *)

(* Bardzo naiwnie (będzie można ulepszyć, jak bozia da sort SProp). *)
Record Rat1 : Type :=
{
    numerator1 : Z;
    denominator1 : nat;
    cond1 : denominator1 <> 0;
}.

(* Sprytniej: mianownik interpretujemy jako liczbę dodatnią. *)
Record Rat2 : Type :=
{
    numerator2 : Z;
    denominator2 : nat;
}.

(** Oczywiście w obu przypadkach potrzebne są setoidy. *)

(** HITowe, bez setoidów, w Agdowej notacji: *)

(*
Inductive Q : Type :=
    | numden : Z -> Z -> Q
    | path :
        forall (z1 z2 : Z) (n1 n2 : N),
          z1 * (S n2) = z2 * (S n1) -> numden z1 n1 = numden z2 n2.
*)

(** Najsprytniej: ułamki łańcuchowe. Kodu brak, bo trudne. *)

(** Na końcu jest jeszcze trochę wesołych rzeczy:
    - liczby porządkowe (indukcja-indukcja-rekursja wita)
    - surreals (znów indukcja-indukcja) *)

Inductive Ord : Type :=
    | ZZ : Ord
    | SS : Ord -> Ord
    | lim : (nat -> Ord) -> Ord.

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
    simpl. eauto.
    destruct d; simpl.
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