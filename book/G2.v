(** * G2: Zippery, czyli łażenie po drzewach [TODO] *)

Require Import D5.

(** * Predykaty na listach i drzewach - przypomnienie (TODO) *)

(** * Indeksowanie drzew (TODO) *)

(** Pamiętasz zapewne funkcję [nth] z rozdziału o listach, której
    celem było znalezienie [n]-tego elementu na liście [l]. Jeżeli
    twoja implementacja była poprawna i elegancka, to wyglądała
    zapewne jakoś tak: *)

Print nth.
(* ===> nth =
        fix nth (A : Type) (n : nat) (l : list A) {struct l} :
        option A :=
          match l with
          | [] => None
          | h :: t => match n with
                      | 0 => Some h
                      | S n' => nth A n' t
                      end
          end
             : forall A : Type, nat -> list A -> option A *)

(** Obraz wyłaniający się z tej definicji jest prosty:
    - w pustej liście nic nie znajdziemy
    - jeżeli lista jest niepusta, to przemierzamy ją, zerkając co i rusz
      na indeks [n]. [0] oznacza "już", zaś [S _] oznacza "jeszcze krok"

    Ma to sens, czyż nie? Zastanówmy się więc teraz, jak można
    indeksować inne struktury danych, takie jak wektory czy drzewa (co
    w zasadzie wyczerpuje pytanie, bo elementy każdego typu induktywnego
    to nic innego jak drzewa). *)

Definition nat' : Type := list unit.

(** Pierwsza rzecz, którą musimy zauważyć, to to, że liczby naturalne i
    listy [unit]ów to w zasadzie to samo. No bo pomyśl:
    - jest [0] i jest [nil]
    - jest [S 0] i jest [tt :: nil]
    - jest [S (S 0)] i jest [tt :: tt :: nil]
    - etc. *)

(** **** Ćwiczenie *)

(** Pokaż, że typy [nat] i [list unit] są izomorficzne. *)

(* begin hide *)
(* TODO *)
(* end hide *)

(** Podsumowując: listy indeksujemy liczbami naturalnymi, które są tym
    samym co listy [unit]ów. Przypadek? Nie sądzę. Można tę konstatację
    sparafrazować tak: [list A] indeksujemy za pomocą [list unit].

    Jest w tym sporo mądrości: [list A] to podłużny byt wypełniony
    elementami typu [A], zaś [list unit] to po prostu podłużny byt -
    jego zawartość jest nieistotna.

    ACHTUNG: to wszystko kłamstwa, sprawa jest skomplikowańsza niż
    myślałem. *)

Module BT.

(* 1 + A * X^2 *)
Inductive BT (A : Type) : Type :=
    | E : BT A
    | N : A -> BT A -> BT A -> BT A.

Arguments E {A}.
Arguments N {A} _ _ _.

(** Tutaj typ indeksów jest oczywisty: możemy iść do lewego albo prawego poddrzewa,
    co odpowiada konstruktorom [L] i [R], albo oznajmić, że już dotarliśmy do celu,
    co odpowiada konstruktorowi [here]. *)

(* 1 + 2 * X *)
Inductive IndexBT : Type :=
    | here : IndexBT
    | L : IndexBT -> IndexBT
    | R : IndexBT -> IndexBT.

(** Najważniejszą operacją, jaką możemy wykonać mając typ indeksów, jest pójście
    do poddrzewa odpowiadającego temu indeksowi. *)

Fixpoint subtree {A : Type} (i : IndexBT) (t : BT A) : option (BT A) :=
match i, t with
    | here, _ => Some t
    | L _, E => None
    | L i', N _ l _ => subtree i' l
    | R _, E => None
    | R i', N _ _ r => subtree i' r
end.

(** Znalezienie elementu trzymanego w korzeniu danego poddrzewa jest jedynie
    operacją pochodną. *)

Definition index {A : Type} (i : IndexBT) (t : BT A) : option A :=
match subtree i t with
    | Some (N v _ _) => Some v
    | _              => None
end.

(** Choć można oczywiście posłużyć się osobną implementacją, która jest równoważna
    powyższej. *)

Fixpoint index' {A : Type} (t : BT A) (i : IndexBT) {struct i} : option A :=
match t, i with
    | E, _          => None
    | N v _ _, here => Some v
    | N _ l _, L i' => index' l i'
    | N _ _ r, R i' => index' r i'
end.

Lemma index_index' :
  forall {A : Type} (i : IndexBT) (t : BT A),
    index i t = index' t i.
Proof.
  induction i; destruct t; cbn; intros.
    all: try reflexivity.
    apply IHi.
    apply IHi.
Qed.

End BT.

Module T.

(** Dla drzew z dowolnym rozgałęzieniem jest podobnie jak dla drzew binarnych. *)

(* 1 + A * X^I *)
Inductive T (I A : Type) : Type :=
    | E : T I A
    | N : A -> (I -> T I A) -> T I A.

Arguments E {I A}.
Arguments N {I A} _ _.

(** Indeksy: albo już doszliśmy ([here]), albo idziemy dalej ([there]). *)

(* 1 + I * X *)
Inductive Index (I : Type) : Type :=
    | here : Index I
    | there : I -> Index I -> Index I.

Arguments here {I}.
Arguments there {I} _ _.

Fixpoint subtree {I A : Type} (i : Index I) (t : T I A) : option (T I A) :=
match i, t with
    | here      , _ => Some t
    | there _ _ , E => None
    | there j i', N _ f => subtree i' (f j)
end.

Definition index {I A : Type} (i : Index I) (t : T I A) : option A :=
match subtree i t with
    | Some (N v _) => Some v
    | _            => None
end.

(*
Fixpoint index {I A : Type} (t : T I A) (i : Index I) : option A :=
match t, i with
    | E, _ => None
    | N v _, here => Some v
    | N _ f, there j i' => index (f j) i'
end.
*)
End T.

Module T2.

(** A teraz coś trudniejszego: są dwa konstruktory rekurencyjne o różnej
    liczbie argumentów. *)

(* 1 + A * X + B * X^2 *)
Inductive T (A B : Type) : Type :=
    | E : T A B
    | NA : A -> T A B -> T A B
    | NB : B -> T A B -> T A B -> T A B.

Arguments E {A B}.
Arguments NA {A B} _ _.
Arguments NB {A B} _ _ _.

(** Jedyny sensowny pomysł na typ indeksów jest taki, że odróżniamy
    [NA] od [NB] - jeżeli chcemy wejść do złego konstruktora, to się
    nam po prostu nie udaje. *)

Inductive Index : Type :=
    | here : Index
    | therea : Index -> Index
    | thereb : bool -> Index -> Index.

Arguments here.
Arguments therea _.
Arguments thereb _ _.

(** Jak widać działa, ale co to za działanie. *)

Fixpoint subtree {A B : Type} (i : Index) (t : T A B) : option (T A B) :=
match i, t with
    | here           , _           => Some t
    | therea       i', (NA _ t')   => subtree i' t'
    | thereb false i', (NB _ t' _) => subtree i' t'
    | thereb true  i', (NB _ _ t') => subtree i' t'
    | _              , _           => None
end.

(** [index] też działa, ale typ zwracany robi się skomplikowańszy. *)

Definition index
  {A B : Type} (i : Index) (t : T A B) : option (A + B) :=
match subtree i t with
    | Some (NA a _)   => Some (inl a)
    | Some (NB b _ _) => Some (inr b)
    | _               => None
end.

End T2.

Module T3.

(** A teraz inny tłist: co jeżeli jest więcej [nil]i? *)

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Set Reversible Pattern Implicit.

(* 1 + 1 + A * X * X *)
Inductive T (A : Type) : Type :=
    | EL | ER
    | N (a : A) (l : T A) (r : T A).

Arguments EL {A}.
Arguments ER {A}.

(** Typ indeksów jest łatwy. *)

Inductive Index : Type :=
    | here : Index
    | there : bool -> Index -> Index.

Fixpoint subtree {A : Type} (i : Index) (t : T A) : option (T A) :=
match i, t with
    | here      , _         => Some t
    | there b i', (N _ l r) => if b then subtree i' l else subtree i' r
    | _         , _         => None
end.

Inductive Arg (A : Type) : Type :=
    | BadIndex
    | EmptyLeft
    | EmptyRight
    | Node (a : A).

Arguments BadIndex   {A}.
Arguments EmptyLeft  {A}.
Arguments EmptyRight {A}.

Definition index {A : Type} (i : Index) (t : T A) : Arg A :=
match subtree i t with
    | None           => BadIndex
    | Some EL        => EmptyLeft
    | Some ER        => EmptyRight
    | Some (N a _ _) => Node a
end.

End T3.

(** Przemyślenia: indeksowanie jest dużo bardziej związane z zipperami,
    niż mi się wydawało. Zipper pozwala sfokusować się na jakimś miejscu
    w strukturze i musimy pamiętać, jak do tego miejsca doszliśmy, tj.
    co pominęliśmy po drodze.

    Jeżeli zależy nam wyłącznie na tym, aby pokazać palcem na dane
    miejsce w strukturze, to nie musimy pamiętać, co pominęliśmy.
    Podsumowując: intuicja dotycząca typów indeksów oraz zipperów
    jest dość jasna, ale związki z różniczkowaniem są mocno pokrętne.

    Kwestią jest też jak przenieść te intuicje na indeksowane rodziny.
    Na pewno indeksami [Vec n] jest [Fin n], a skądinąd [Vec n] to
    [{n : nat & {l : list A | length l = n}}], zaś [Fin n] to [nat],
    tylko trochę ograniczone.

    Zapewne działa to bardzo dobrze... taki huj, jednak nie. *)

Module Vec.

(** A teraz to samo dla rodzin indeksowanych. *)

Require Import vec.
Print vec.
(*
Inductive vec (A : Type) : nat -> Type :=
    vnil : vec A 0 | vcons : forall n : nat, A -> vec A n -> vec A (S n)
*)

Inductive Fin : nat -> Type :=
    | FZ : forall n : nat, Fin (S n)
    | FS : forall n : nat, Fin n -> Fin (S n).

Arguments FZ {n}.
Arguments FS {n} _.

Fixpoint index {A : Type} {n : nat} (i : Fin n) (v : vec A n) : A.
Proof.
  destruct i as [| n i'].
    inversion v. exact X.
    inversion v. exact (index _ _ i' X0).
Defined.

End Vec.

Module hTree.

Inductive T (A : Type) : nat -> Type :=
    | E : T A 0
    | N :
        forall {n m : nat},
          A -> T A n -> T A m -> T A (S (max n m)).

(** To jednak działa inaczej niż myślałem. *)

End hTree.

Module W.

Require Import G.

Print W.

Inductive IW {A : Type} (B : A -> Type) : Type :=
    | here  : IW B
    | there : forall x : A, B x -> IW B -> IW B.

Arguments here {A B}.
Arguments there {A B x} _.

Print natW.

Print listW.listW.

Definition A (X : Type) : Type := unit + X.

Definition B {X : Type} (a : A X) : Type :=
match a with
    | inl _ => False
    | inr _ => unit
end.

Fixpoint nat_IW {X : Type} (n : nat) : (@IW (A X) (@B X)).
Proof.
  destruct n as [| n'].
    exact here.
    eapply there. Unshelve.
      Focus 3. unfold A.
Abort.

End W.

(** * Zippery dla list - chodzenie po linie (TODO) *)

(** * Szukanie dziury w typie, czyli różniczkowanie (TODO) *)

(** * Zippery dla typów induktywnych (TODO) *)

(** * Zippery dla typów koinduktywnych (TODO) *)