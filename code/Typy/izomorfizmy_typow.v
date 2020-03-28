(** ** Izomorfizmy typów *)

Definition isopair {A B : Type} (f : A -> B) (g : B -> A) : Prop :=
  (forall a : A, g (f a) = a) /\
  (forall b : B, f (g b) = b).

Definition iso (A B : Type) : Prop :=
  exists (f : A -> B) (g : B -> A), isopair f g.

Definition pred (n : nat) : option nat :=
match n with
    | 0 => None
    | S n' => Some n'
end.

Definition unpred (on : option nat) : nat :=
match on with
    | None => 0
    | Some n => S n
end.

Lemma iso_nat_option_Nat :
  iso nat (option nat).
Proof.
  red. exists pred, unpred.
  split.
    destruct a as [| a']; cbn; reflexivity.
    destruct b as [b' |]; cbn; reflexivity.
Qed.

Require Import List.
Import ListNotations.

Definition uncons {A : Type} (l : list A) : option (A * list A) :=
match l with
    | [] => None
    | h :: t => Some (h, t)
end.

Definition ununcons {A : Type} (x : option (A * list A)) : list A :=
match x with
    | None => []
    | Some (h, t) => h :: t
end.

Lemma list_char_iso :
  forall A : Type, iso (list A) (option (A * list A)).
Proof.
  intro. exists uncons, ununcons. split.
    destruct a as [| h t]; cbn; reflexivity.
    destruct b as [[h t] |]; cbn; reflexivity.
Qed.

(** Jak można się domyślić po przykładach, charakterystyczne izomorfizmy
    dla prostych typów induktywnych są łatwe. A co z bardziej innowacyjnymi
    rodzajami definicji induktywnych oraz z definicjami koinduktywnymi? Te
    drugie oczywiście polegną bez aksjomatów. O luj, a jednak nie. *)

Require Import F3.

Definition hdtl {A : Type} (s : Stream A) : A * Stream A :=
  (hd s, tl s).

Definition unhdtl {A : Type} (x : A * Stream A) : Stream A :=
{|
    hd := fst x;
    tl := snd x;
|}.

Lemma Stream_iso_char :
  forall A : Type, iso (Stream A) (A * Stream A).
Proof.
  intro. exists hdtl, unhdtl. split.
  all: unfold hdtl, unhdtl; cbn.
    destruct a; reflexivity.
    destruct b; reflexivity.
Qed.

(** Jak trudno jest zrobić ciekawsze izomorfizmy? *)

Require Import FunInd.

Function div2 (n : nat) : nat + nat :=
match n with
    | 0 => inl 0
    | 1 => inr 0
    | S (S n') =>
        match div2 n' with
            | inl m => inl (S m)
            | inr m => inr (S m)
        end
end.

Definition undiv2 (x : nat + nat) : nat :=
match x with
    | inl n => 2 * n
    | inr n => S (2 * n)
end.

Lemma iso_nat_natnat :
  iso nat (nat + nat).
Proof.
  exists div2, undiv2. split.
    intro. functional induction (div2 a); cbn.
      1-2: reflexivity.
      rewrite e0 in IHs. cbn in IHs. rewrite <- plus_n_Sm, IHs. reflexivity.
      rewrite e0 in IHs. cbn in IHs. rewrite <- plus_n_Sm, IHs. reflexivity.
    destruct b.
      cbn. functional induction (div2 n); cbn.
        1-2: reflexivity.
        rewrite <- 2!plus_n_Sm. cbn. rewrite IHs. reflexivity.
        rewrite <- 2!plus_n_Sm. cbn. rewrite IHs. reflexivity.
      induction n as [| n'].
        cbn. reflexivity.
        cbn in *. destruct n' as [| n'']; cbn in *.
          reflexivity.
          rewrite <- plus_n_Sm. rewrite IHn'. reflexivity.
Qed.

(** Niezbyt trudno, ale łatwo też nie. *)

Function fill_square (n : nat) : nat * nat :=
match n with
    | 0 => (0, 0)
    | S n' =>
        match fill_square n' with
            | (0, m) => (S m, 0)
            | (S m1, m2) => (m1, S m2)
        end
end.

Require Import X3.

Check map.

Compute map fill_square (iterate S 50 0).

Definition zigzag_order (x y : nat * nat) : Prop :=
  exists n m : nat,
    x = fill_square n /\
    y = fill_square m /\ n < m.

Function unfill_square (x : nat * nat) {wf zigzag_order x} : nat :=
match x with
    | (0, 0) => 0
    | (S n, 0) => S (unfill_square (0, n))
    | (n, S m) => S (unfill_square (S n, m))
end.
Proof.
  Focus 4. red. destruct a as [n m]. constructor.
    destruct y as [n' m']. unfold zigzag_order.
Admitted.

Lemma iso_nat_natnat' :
  iso nat (nat * nat).
Proof.
  exists fill_square, unfill_square. split.
    intro. functional induction (fill_square a).
Abort.

(** Trochę generycznych rzeczy. *)

Definition swap {A B : Type} (x : A * B) : B * A :=
match x with
    | (a, b) => (b, a)
end.

Lemma prod_comm :
  forall A B : Type, iso (A * B) (B * A).
Proof.
  intros. exists swap, swap. split.
    destruct a; cbn; reflexivity.
    destruct b; cbn; reflexivity.
Qed.

Definition reassoc {A B C : Type} (x : A * (B * C)) : (A * B) * C :=
match x with
    | (a, (b, c)) => ((a, b), c)
end.

Definition unreassoc {A B C : Type} (x : (A * B) * C) : A * (B * C) :=
match x with
    | ((a, b), c) => (a, (b, c))
end.

Lemma prod_assoc :
  forall A B C : Type, iso (A * (B * C)) ((A * B) * C).
Proof.
  intros. exists reassoc, unreassoc. split.
    destruct a as [a [b c]]; cbn; reflexivity.
    destruct b as [[a b] c]; cbn; reflexivity.
Qed.

Lemma prod_unit_l :
  forall A : Type, iso (unit * A) A.
Proof.
  intro. exists snd. exists (fun a : A => (tt, a)). split.
    destruct a as [[] a]; cbn; reflexivity.
    reflexivity.
Qed.

Lemma prod_unit_r :
  forall A : Type, iso (A * unit) A.
Proof.
  intro. exists fst. exists (fun a : A => (a, tt)). split.
    destruct a as [a []]. cbn. reflexivity.
    reflexivity.
Qed.

(** Trzeba przerobić rozdział o typach i funkcjach tak, żeby nie mieszać
    pojęć kategorycznych (wprowadzonych na początku) z teoriozbiorowymi
    (injekcja, surjekcja, bijekcja). Przedstawić te 3 ostatnie jako
    explicite charakteryzacje pojęć kategorycznych. *)

Lemma sum_empty_l :
  forall A : Type, iso (Empty_set + A) A.
Proof.
  intro. eexists. eexists. Unshelve. all: cycle 1.
    destruct 1 as [[] | a]. exact a.
    exact inr.
    split.
      destruct a as [[] | a]; reflexivity.
      reflexivity.
Qed.

Lemma sum_empty_r :
  forall A : Type, iso (A + Empty_set) A.
Proof.
  intro. eexists. eexists. Unshelve. all: cycle 1.
    destruct 1 as [a | []]. exact a.
    exact inl.
    split.
      destruct a as [a | []]; reflexivity.
      reflexivity.
Qed.

Lemma sum_assoc :
  forall A B C : Type, iso (A + (B + C)) ((A + B) + C).
Proof.
  intros. do 2 eexists. Unshelve. all: cycle 1.
    1-2: firstorder.
    split.
      destruct a as [a | [b | c]]; reflexivity.
      destruct b as [[a | b] | c]; reflexivity.
Qed.

Lemma sum_comm :
  forall A B : Type, iso (A + B) (B + A).
Proof.
  intros. do 2 eexists. Unshelve. all: cycle 1.
    1-2: firstorder.
    split.
      destruct a; reflexivity.
      destruct b; reflexivity.
Qed.

(** Jak trudno jest z takich standardowych izomorfizmów uskładać coś w
    stylu nat ~ list nat? A może nie da się i trzeba robić ręcznie? *)

Require Import vec.

Definition vlist (A : Type) : Type :=
  {n : nat & vec A n}.

Fixpoint vectorize' {A : Type} (l : list A) : vec A (length l) :=
match l with
    | nil => vnil
    | cons h t => vcons h (vectorize' t)
end.

Definition vectorize {A : Type} (l : list A) : vlist A :=
  existT _ (length l) (vectorize' l).

Fixpoint toList {A : Type} {n : nat} (v : vec A n) : list A :=
match v with
    | vnil => nil
    | vcons h t => cons h (toList t)
end.

Definition listize {A : Type} (v : vlist A) : list A :=
  toList (projT2 v).

Definition transport
  {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
match p with
    | eq_refl => u
end.

Lemma sigT_eq :
  forall
    {A : Type} (P : A -> Type)
    {x y : A} (p : x = y)
    {u : P x} {v : P y} (q : transport P p u = v),
      existT P x u = existT P y v.
Proof.
  destruct p. cbn. destruct 1. reflexivity.
Defined.

Lemma sigT_eq' :
  forall
    {A : Type} (P : A -> Type) {x y : sigT P},
      x = y ->
        {p : projT1 x = projT1 y & transport P p (projT2 x) = projT2 y}.
Proof.
  destruct 1, x. cbn. exists eq_refl. cbn. reflexivity.
Defined.

Lemma iso_list_vlist :
  forall A : Type, iso (list A) (vlist A).
Proof.
  intro. exists vectorize, listize. split.
    induction a as [| h t]; cbn in *.
      reflexivity.
      rewrite IHt. reflexivity.
    destruct b as [n v]. unfold vectorize. cbn.
      induction v as [| h t]; cbn.
        reflexivity.
        apply sigT_eq' in IHv. cbn in IHv. destruct IHv.
        eapply sigT_eq. Unshelve. all: cycle 1.
          exact (f_equal S x).
          admit. (* Więcej kubiczności. *)
Admitted.