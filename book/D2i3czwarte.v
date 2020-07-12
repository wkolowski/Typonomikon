(** * D2i3czwarte: Zippery, indeksy i izomorfizmy typów (TODO) *)

Require Import D5.

(** * Indeksowanie struktur danych (TODO) *)

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

(** * Zippery (TODO) *)

(* begin hide *)
(*
TODO: Zippery (z dwóch perspektyw: łażenie po drzewach i różniczkowanie 
TODO: typów) oraz indeksowanie poddrzew dla typów induktywnych.
*)
(* end hide *)

(** * Izomorfizmy typów (TODO) *)

(* begin hide *)

(** TODO: Izomorfizmy dla typów induktywnych (patrz notatka poniżej).

    Każde drzewo jest drzewem o jakiejś wysokości (no chyba że ma
    nieskończone rozgałęzienie, to wtedy nie). Uogólniając: każdy
    element typu induktywnego jest elementem odpowiadającego mu
    typu indeksowanego o pewnym indeksie. UWAGA: rozróżnienie na
    drzewa o skończonej wysokości vs drzewa o ograniczonej wysokości. *)

(* end hide *)


Definition isopair {A B : Type} (f : A -> B) (g : B -> A) : Prop :=
  (forall a : A, g (f a) = a) /\
  (forall b : B, f (g b) = b).

Definition iso (A B : Type) : Prop :=
  exists (f : A -> B) (g : B -> A), isopair f g.

(** ** Produkty i sumy *)

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

(** ** Liczby naturalne *)

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

(** ** Listy *)

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

(** ** Strumienie *)

Require Import F3.

(** Jak można się domyślić po przykładach, charakterystyczne izomorfizmy
    dla prostych typów induktywnych są łatwe. A co z innowacyjniejszymi
    rodzajami definicji induktywnych oraz z definicjami koinduktywnymi?
    Sprawdźmy to! *)

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

(** ** Ciekawsze izomorfizmy *)

Require Import FunInd.

(** Jak trudno jest zrobić ciekawsze izomorfizmy? *)

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

Compute D5.map fill_square (D5.iterate S 50 0).

Definition zigzag_order (x y : nat * nat) : Prop :=
  exists n m : nat,
    x = fill_square n /\
    y = fill_square m /\ n < m.

(*
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
*)

Unset Guard Checking.
Fixpoint unfill_square (x : nat * nat) : nat :=
match x with
    | (0, 0) => 0
    | (S n, 0) => S (unfill_square (0, n))
    | (n, S m) => S (unfill_square (S n, m))
end.
Set Guard Checking.

Lemma iso_nat_natnat' :
  iso nat (nat * nat).
Proof.
  exists fill_square, unfill_square. split.
    intro. functional induction (fill_square a).
Admitted.

(** Jak trudno jest z podstawowych izomorfizmów dla produktów i sum
    uskładać coś w stylu nat ~ list nat? A może nie da się i trzeba
    robić ręcznie? *)

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

Definition ap
  {A B : Type} (f : A -> B) {x y : A} (p : x = y) : f x = f y :=
match p with
    | eq_refl => eq_refl
end.

(* Lemma 2.3.10 *)
Lemma transport_ap :
  forall {A B : Type} (P : B -> Type) (f : A -> B)
    (x y : A) (p : x = y) (u : P (f x)),
      transport P (ap f p) u =
      @transport A (fun x => P (f x)) x y p u.
Proof.
  destruct p. cbn. reflexivity.
Defined.

Lemma eq_head_tail :
  forall {A : Type} {n : nat} (v1 v2 : vec A (S n)),
    head v1 = head v2 -> tail v1 = tail v2 -> v1 = v2.
Proof.
  Require Import Equality.
  dependent destruction v1.
  dependent destruction v2.
  cbn. destruct 1, 1. reflexivity.
Qed.

Lemma transport_cons :
  forall {A : Type} {n m : nat} (h : A) (t : vec A n) (p : n = m),
    transport (fun n : nat => vec A (S n)) p
     (h :: t) = h :: transport (fun n : nat => vec A n) p t.
Proof.
  destruct p. cbn. reflexivity.
Qed.

Lemma iso_list_vlist :
  forall A : Type, iso (list A) (vlist A).
Proof.
  intro. red. exists vectorize, listize. split.
    induction a as [| h t]; cbn in *.
      reflexivity.
      rewrite IHt. reflexivity.
    destruct b as [n v]. unfold vectorize. cbn.
      induction v as [| h t]; cbn.
        reflexivity.
        apply sigT_eq' in IHv. cbn in IHv. destruct IHv.
          eapply sigT_eq. Unshelve. all: cycle 1.
            exact (ap S x).
            rewrite transport_ap, transport_cons, e. reflexivity.
Qed.

(** Wnioski: da się zrobić trochę... *)

Fixpoint nat_vec {n : nat} (arg : nat) : vec nat (S n) :=
match n with
    | 0 => arg :: vnil
    | S n' =>
        let
          (arg1, arg2) := fill_square arg
        in
          arg1 :: nat_vec arg2
end.

Fixpoint vec_nat {n : nat} (v : vec nat n) {struct v} : option nat :=
match v with
    | vnil => None
    | vcons h t =>
        match vec_nat t with
            | None => Some h
            | Some r => Some (unfill_square (h, r))
        end
end.

(*
Fixpoint vec_nat' {n : nat} (v : vec nat (S n)) : nat :=
match v with
    | vcons x vnil => x
    | vcons x v' => unfill_square (x, vec_nat' v')
end.

    | vnil => None
    | vcons h t =>
        match vec_nat t with
            | None => Some h
            | Some r => Some (unfill_square (h, r))
        end
end.
*)

Compute D5.map (@nat_vec 3) [111; 1111; 11111].
Compute D5.map vec_nat (D5.map (@nat_vec 3) [111; 1111]).

Lemma nat_vlist :
  forall n : nat, iso nat (vec nat (S n)).
Proof.
  unfold iso. intros.
  exists nat_vec.
  exists (fun v => match vec_nat v with | None => 0 | Some n => n end).
  split.
    Focus 2. dependent destruction b.
    induction n as [| n']. (*
      reflexivity.
      {
        intro. destruct (fill_square a) as [a1 a2].
        change (vec_nat _) with (match vec_nat (@nat_vec n' a2) with
                                  | None => Some a1
                                  | Some r => Some (unfill_square (a1, r))
                                  end).
        rewrite <- (IHn' a2).*)
Abort.

(** ... ale [nat ~ list nat] jest dość trudne. *)