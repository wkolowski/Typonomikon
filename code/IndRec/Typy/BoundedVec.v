(** Normalne "wektory" (czyli listy z długością znaną w czasie sprawdzania
    typów - trzeba wymyślić na nie jakąś polską nazwę) mają precyzyjnie
    określoną długość. A co jakby zamiast tego zrobić jedynie ograniczenie
    górne na długość? *)

Inductive BVec (A : Type) : nat -> Type :=
    | Nil  :
        forall n : nat, BVec A n
    | Cons :
        forall (h : A) {n : nat} (t : BVec A n), BVec A (S n).

Arguments Nil {A n}.
Arguments Cons {A} _ {n} _.

(** Długość musimy policzyć ręcznie, bo znamy tylko górne ograniczenie na nią. *)

Fixpoint len {A : Type} {n : nat} (v : BVec A n) : nat :=
match v with
    | Nil => 0
    | Cons _ t => 1 + len t
end.

Lemma bounded :
  forall {A : Type} {n : nat} (v : BVec A n),
    len v <= n.
Proof.
  induction v as [| h t]; cbn.
    apply le_0_n.
    apply le_n_S. assumption.
Qed.

(** Funkcja wyciągająca z wektora głowę musi zwracać opcję, bo nie możemy nijak
    zagwarantować za pomocą indeksu, że wektor nie jest pusty. *)

Definition head {A : Type} {n : nat} (v : BVec A n) : option A :=
match v with
    | Nil => None
    | Cons h _ => Some h
end.

Require Import Equality.

(** Podobnie nie możemy zagwarantować, że z wektora da się wyciągnąć jego ogon
    (bo może nie być ogona), ale w typie powinniśmy zaznaczyć, że długość naszego
    wektora jest ograniczona przez n + 1, dzięki czemu wiemy, że jeżeli już jakiś
    ogon uda się wyjąć, to jego długość będzie wynosić co najwyżej n. *)

Definition tail {A : Type} {n : nat} (v : BVec A (S n)) : option (BVec A n).
Proof.
  dependent destruction v.
    exact None.
    exact (Some v).
Defined.

(** [uncons] to połączenie [head] i [tail]. *)

Definition uncons {A : Type} {n : nat} (v : BVec A (S n)) : option (A * BVec A n).
Proof.
  dependent destruction v.
    exact None.
    exact (Some (h, v)).
Defined.

Fixpoint init {A : Type} {n : nat} (v : BVec A (S n)) : option (BVec A n).
Proof.
  dependent destruction v.
    exact None.
    dependent destruction v.
      exact (Some Nil).
Abort.

(** [take] idzie zrobić całkiem elegancko - ograniczeniem na długość jest
    minimum z dotychczasowej długości i liczby elementów, które chcemy
    zatrzymać. *)

Fixpoint take {A : Type} {n : nat} (m : nat) (v : BVec A n) : BVec A (min m n).
Proof.
  destruct m as [| m']; cbn.
    exact Nil.
    destruct v as [| h n t]; cbn.
      exact Nil.
      exact (Cons h (take _ _ m' t)).
Defined.

Require Import Arith.

(** [drop] jest jeszcze elegancksze - nowym ograniczeniem jest różnica starego i
    liczby elementów, które chcemy wyrzucić. *)

Fixpoint drop {A : Type} {n : nat} (m : nat) (v : BVec A n) : BVec A (n - m).
Proof.
  destruct m as [| m']; cbn.
    rewrite Nat.sub_0_r. exact v.
    destruct v as [| h n t]; cbn.
      exact Nil.
      exact (drop _ _ m' t).
Defined.

Fixpoint weaken {A : Type} {n : nat} (v : BVec A n) (m : nat) : BVec A (n + m) :=
match v with
    | Nil => Nil
    | Cons h t => Cons h (weaken t m)
end.

Fixpoint weaken' {A : Type} {n : nat} (v : BVec A n) (m : nat) : BVec A (m + n).
Proof.
refine (
match v with
    | Nil => Nil
    | Cons h t => _
end).
  rewrite <- plus_n_Sm. exact (Cons h (weaken' _ _ t m)).
Defined.

(** [app] *)

Fixpoint app {A : Type} {n m : nat} (v1 : BVec A n) (v2 : BVec A m) : BVec A (n + m).
Proof.
  refine (
    match v1 with
        | Nil => _
        | Cons h t => _
    end).
    exact (weaken' v2 n0).
    exact (Cons h (app _ _ _ t v2)).
Defined.

(** Poniższe funkcje nie różnią się wiele od analogicznych dla zwykłych "wektorów". *)

Fixpoint snoc {A : Type} {n : nat} (v : BVec A n) (x : A) : BVec A (S n) :=
match v with
    | Nil => Cons x Nil
    | Cons h t => Cons h (snoc t x)
end.

Fixpoint rev {A : Type} {n : nat} (v : BVec A n) : BVec A n :=
match v with
    | Nil => Nil
    | Cons h t => snoc (rev t) h
end.

Fixpoint map {A B : Type} (f : A -> B) {n : nat} (v : BVec A n) : BVec B n :=
match v with
    | Nil => Nil
    | Cons h t => Cons (f h) (map f t)
end.

Fixpoint join {A : Type} {n m : nat} (v : BVec (BVec A n) m)
  : BVec A (m * n) :=
match v with
    | Nil => Nil
    | Cons h t => app h (join t)
end.

Fixpoint repeat {A : Type} (n : nat) (x : A) : BVec A n :=
match n with
    | 0 => Nil
    | S n' => Cons x (repeat n' x)
end.

Fixpoint nth {A : Type} {n : nat} (m : nat) (v : BVec A n) : option A :=
match m, v with
    | _   , Nil => None
    | 0   , Cons h _ => Some h
    | S m', Cons _ t => nth m' t
end.

Fixpoint last {A : Type} {n : nat} (l : BVec A (S n)) {struct l} : option A.
Proof.
  destruct l as [| h [| t]].
    exact None.
    exact (Some h).
    exact (last _ _ l).
Defined.

(** TODO for BoundedVec: wszystko *)