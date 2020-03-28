(** * Parametryczność *)

(** UWAGA TODO: ten podrozdział zawiera do pewnego stopnia kłamstwa (tzn.
    dość uproszczony punkt widzenia). *)

(** Niech [A B : Type]. Zadajmy sobie następujące pytanie: ile jest funkcji
    typu [A -> B]? Żeby ułatwić sobie zadanie, ograniczmy się jedynie do
    typów, które mają skończoną ilość elementów.

    Nietrudno przekonać się, że ich ilość to |B|^|A|, gdzie ^ oznacza
    potęgowanie, zaś |T| to ilość elementów typu [T] (ta notacja nie ma
    nic wspólnego z Coqiem — zaadaptowałem ją z teorii zbiorów jedynie
    na potrzeby tego podrozdziału).

    Udowodnić ten fakt możesz (choć póki co nie w Coqu) posługując się
    indukcją po ilości elementów typu [A]. Jeżeli [A] jest pusty, to
    jest tylko jedna taka funkcja, o czym przekonałeś się już podczas
    ćwiczeń w podrozdziale o typie [Empty_set]. *)

(** **** Ćwiczenie *)

(** Udowodnij (nieformalnie, na papierze), że w powyższym akapicie nie
    okłamałem cię. *)

(** **** Ćwiczenie *)

(** Zdefiniuj wszystkie możliwe funkcje typu [unit -> unit], [unit -> bool]
    i [bool -> bool]. *)

(** Postawmy sobie teraz trudniejsze pytanie: ile jest funkcji typu
    [forall A : Type, A -> A]? W udzieleniu odpowiedzi pomoże nam
    parametryczność — jedna z właściwości Coqowego polimorfizmu.

    Stwierdzenie, że polimorfizm w Coqu jest parametryczny, oznacza, że
    funkcja biorąca typ jako jeden z argumentów działa w taki sam sposób
    niezależnie od tego, jaki typ przekażemy jej jako argument.

    Konsekwencją tego jest, że funkcje polimorficzne nie wiedzą (i nie
    mogą wiedzieć), na wartościach jakiego typu operują. Wobec tego
    elementem typu [forall A : Type, A -> A] nie może być funkcja, która
    np. dla typu [nat] stale zwraca [42], a dla innych typów po prostu
    zwraca przekazany jej argument.

    Stąd konkludujemy, że typ [forall A : Type, A -> A] ma tylko jeden
    element, a mianowicie polimorficzną funkcję identycznościową. *)

Definition id' : forall A : Type, A -> A :=
  fun (A : Type) (x : A) => x.

(** **** Ćwiczenie *)

(** Zdefiniuj wszystkie elementy następujących typów lub udowodnij, że
    istnienie choć jednego elementu prowadzi do sprzeczności:
    - [forall A : Type, A -> A -> A]
    - [forall A : Type, A -> A -> A -> A]
    - [forall A B : Type, A -> B]
    - [forall A B : Type, A -> B -> A]
    - [forall A B : Type, A -> B -> B]
    - [forall A B : Type, A -> B -> A * B]
    - [forall A B : Type, A -> B -> sum A B]
    - [forall A B C : Type, A -> B -> C]
    - [forall A : Type, option A -> A]
    - [forall A : Type, list A -> A] *)

(* begin hide *)
Theorem no_such_fun :
  (forall A B : Type, A -> B) -> False.
Proof.
  intros. exact (X nat False 42).
Qed.
(* end hide *)

(** TODO: tu opisać kłamstwo *)

Inductive path {A : Type} (x : A) : A -> Type :=
    | idpath : path x x.

Arguments idpath {A} _.

Axiom LEM : forall (A : Type), A + (A -> False).

Open Scope type_scope.

Definition bad' (A : Type) :
  {f : A -> A &
    (@path Type bool A * forall x : A, f x <> x) +
    ((@path Type bool A -> False) * forall x : A, f x = x)}.
Proof.
  destruct (LEM (@path Type bool A)).
    destruct p. exists negb. left. split.
      reflexivity.
      destruct x; inversion 1.
    exists (fun x : A => x). right. split.
      assumption.
      reflexivity.
Defined.

Definition bad (A : Type) : A -> A := projT1 (bad' A).

Lemma bad_is_bad :
  forall b : bool, bad bool b <> b.
Proof.
  unfold bad.
  intros. destruct bad'; cbn. destruct s as [[p H] | [p H]].
    apply H.
    contradiction p. reflexivity.
Defined.

Lemma bad_ist_gut :
  forall (A : Type) (x : A),
    (@path Type bool A -> False) -> bad A x = x.
Proof.
  unfold bad. intros A x p.
  destruct bad' as [f [[q H] | [q H]]]; cbn.
    contradiction p.
    apply H.
Defined.
