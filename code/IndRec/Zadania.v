(** * Enumeracje *)

(** Zdefiniuj typ reprezentujący dni tygodnia. *)
Inductive Day : Type := Mon | Tue | Wed | Thu | Fri | Sat | Sun.

(** Zdefiniuj typ reprezentujący miesiące roku. *)
Inductive Month : Type :=
  Jan | Feb | Mar | Apr | May | Jun | Jul | Aug | Sep | Oct | Nov | Dec.

(** Zdefiniuj typ reprezentujący kolory podstawowe. *)
Inductive RGB : Type := R | G | B.

(** Zdefiniuj typ reprezentujący kolory podstawowe + kanał alfa. *)
Fail Inductive RGBA : Type := R | G | B | A.

(** Zdefiniuj typ reprezentujący uniksowe uprawnienia dostępu. *)
Fail Inductive UnixAcess : Type := R | W | X.

(** Zdefiniuj typ reprezentujący różę kierunków (z 4 kierunkami). *)
(*Inductive Dir : Type := N | S | E | W.*)

(** Zdefiniuj typ reprezentujący logikę trójwartościową. *)
(*Inductive bool3 : Type := false | unknown | true.*)

(** * Parametry *)

(** Zdefiniuj spójniki logiczne i inne podstawowe rzeczy. *)

Inductive False : Prop := .

Inductive True : Prop :=
    | I : True.

Inductive and (P Q : Prop) : Prop :=
    | conj : P -> Q -> and P Q.

Inductive or (P Q : Prop) : Prop :=
    | or_introl : P -> or P Q
    | or_intror : Q -> or P Q.

Inductive ex (A : Type) (P : A -> Prop) : Prop :=
    | ex_intro : forall x : A, P x -> ex A P.

Inductive Empty : Type := .

Inductive unit : Type :=
    | tt : unit.

Inductive prod (A B : Type) : Type :=
    | pair : A -> B -> prod A B.

Inductive sum (A B : Type) : Type :=
    | inl : A -> sum A B
    | inr : B -> sum A B.

Inductive sig (A : Type) (P : A -> Prop) : Type :=
    | exist : forall x : A, P x -> sig A P.

Inductive sigT (A : Type) (P : A -> Type) : Type :=
    | existT : forall x : A, P x -> sigT A P.

(** * Typy algebraiczne *)

(** Zdefiniuj typ opcji na [A]. *)

Inductive option (A : Type) : Type :=
    | None : option A
    | Some : A -> option A.

(** Podefiniuj co trzeba dla list. *)
(*
Inductive Elem {A : Type} (x : A) : list A -> list A -> Prop :=
Inductive NoDup {A : Type} : list A -> Prop :=
Inductive Dup {A : Type} : list A -> Prop :=
Inductive Rep {A : Type} (x : A) : nat -> list A -> Prop :=
Inductive Exists {A : Type} (P : A -> Prop) : list A -> Prop :=
Inductive Forall {A : Type} (P : A -> Prop) : list A -> Prop :=
Inductive AtLeast {A : Type} (P : A -> Prop) : nat -> list A -> Prop :=
Inductive Exactly {A : Type} (P : A -> Prop) : nat -> list A -> Prop :=
Inductive AtMost  {A : Type} (P : A -> Prop) : nat -> list A -> Prop :=
Inductive Sublist {A : Type} : list A -> list A -> Prop :=
Inductive Prefix {A : Type} : list A -> list A -> Prop :=
Inductive Suffix {A : Type} : list A -> list A -> Prop :=
Inductive Subseq {A : Type} : list A -> list A -> Prop :=
Inductive Permutation {A : Type} : list A -> list A -> Prop :=
Inductive Cycle {A : Type} : list A -> list A -> Prop :=
Inductive Palindrome {A : Type} : list A -> Prop :=
*)

(** Zdefiniuj typ list niepustych, które trzymają elementy typu [A]. Potem
    zdefiniuj dla nich wszystkie te użyteczne rzeczy co dla list. *)

Inductive nel (A : Type) : Type :=
    | singl : A -> nel A
    | cons : A -> nel A -> nel A.

(** Zdefiniuj typ niepustych drzew binarnych, które trzymają wartości typu [A] jedynie
    w liściach. *)

Inductive RBTree (A : Type) : Type :=
    | Leaf : A -> RBTree A
    | Node : RBTree A -> RBTree A -> RBTree A.

(** Zdefiniuj typ niepustych drzew o skończonej ilości synów, które trzymają
    wartości typu [A] w liściach. *)

Fail Inductive RFinTree (A : Type) : Type :=
    | Leaf : A -> RFinTree A
    | Node : list (RFinTree A) -> RFinTree A.

(** Zdefiniuj typ drzew binarnych, które trzymają elementy typu [A]. *)

Fail Inductive BTree (A : Type) : Type :=
    | Empty : BTree A
    | Node : A -> BTree A -> BTree A -> BTree A.

(** Zdefiniuj typ drzew o skończonej ilości synów, które trzymają elementy
    typu [A]. *)

Fail Inductive Tree (A : Type) : Type :=
    | Empty : Tree A
    | Node : list (Tree A) -> Tree A.

(** Zdefiniuj typ drzew o dowolnej ilości synów, które trzymają elementy
    typu [A]. *)

Fail Inductive InfTree (A : Type) : Type :=
    | Empty : InfTree A
    | Node : forall (B : Type), (B -> InfTree A) -> InfTree A.

(** Zdefiniuj typ drzew trzymających elementy typu [A], których rozgałęzienie
    jest wyznaczone przez parametr [B : Type]. *)

Fail Inductive InfTree' (B A : Type) : Type :=
    | Empty : InfTree' B A
    | Node : (B -> InfTree' B A) -> InfTree' B A.

(** * Indeksy - predykaty i relacje *)

(** Zdefiniuj predykaty [even] i [odd]. *)
(*Inductive even : nat -> Prop :=*)

(** Zdefiniuj relację [<=] dla liczb naturalnych i to na dwa różne sposoby. *)

Inductive le (n : nat) : nat -> Prop :=
    | le_refl : le n n
    | le_S : forall m : nat, le n m -> le n (S m).

Fail Inductive le : nat -> nat -> Prop :=
    | le_0 : forall n : nat, le 0 n
    | le_S_S : forall n m : nat, le n m -> le (S n) (S m).

(** * Indeksy - typy *)

(** Zdefiniuj rodzinę typów [Fin : nat -> Type], gdzie [Fin n] jest typem o
    [n] elementach. *)
Inductive Fin : nat -> Type :=
    | FZ : forall n : nat, Fin (S n)
    | FS : forall n : nat, Fin n -> Fin (S n).

(** Zdefiniuj typ reprezentujący datę (dla uproszczenia, niech zaczyna się
    od 1 stycznia 1970. *)

Fixpoint isGapYear (n : nat) : bool :=
match n with
    | 0 => false
    | 1 => false
    | 2 => true
    | 3 => false
    | S (S (S (S n'))) => isGapYear n'
end.

Fixpoint dayInMonth (gap : bool) (m : Month) : Type :=
match m with
    | Jan | Apr | Jun | Sep | Nov => Fin 30
    | Feb => if gap then Fin 28 else Fin 29
    | Mar | May | Jul | Aug | Oct | Dec => Fin 31
end.

Definition Date : Type :=
  {year : nat & {month : Month & dayInMonth (isGapYear year) month}}.

(** Zdefiniuj typ list indeksowanych długością. *)
Inductive vec (A : Type) : nat -> Type :=
    | vnil : vec A 0
    | vcons : A -> forall {n : nat}, vec A n -> vec A (S n).

(** Zdefiniuj predykat należenia dla [vec]. *)
(*Inductive elem {A : Type} : A -> forall n : nat, vec A n -> Prop :=*)

(** Zdefiniuj typ list indeksowanych przez minimalny/maksymalny element. *)

Inductive minlist {A : Type} (R : A -> A -> Prop) : A -> Type :=
    | msingl : forall x : A, minlist R x
    | mcons_le :
        forall {min : A} (x : A), R x min -> minlist R min -> minlist R x
    | mcons_gt :
        forall {min : A} (x : A), ~ R x min -> minlist R min -> minlist R min.

(** Zdefiniuj typ list indeksowanych przez dowolny monoid. *)

(** Zdefiniuj typ drzew binarnych trzymających elementy w węzłach, które są
    indeksowane wysokością. *)

Inductive hBTree (A : Type) : nat -> Type :=
    | hEmpty : hBTree A 0
    | hNode : A -> forall {n m : nat},
                     hBTree A n -> hBTree A m -> hBTree A (S (max n m)).

(** Zdefiniuj typ list, które mogą trzymać wartości różnych typów.
    Typ każdego elementu listy nie jest jednak dowolny - jest on
    zdeterminowany przez indeks, pod którym element ten występuje
    na liście. *)

Inductive DepList (P : nat -> Type) : nat -> Type :=
    | dnil : DepList P 0
    | dcons : forall {n : nat}, P n -> DepList P n -> DepList P (S n).

Definition P (n : nat) : Type :=
match n with
    | 0 => bool
    | 1 => Set
    | 2 => nat
    | _ => Type
end.

Goal DepList P 4.
Proof.
  constructor.
  cbn. exact Set.
  constructor.
  cbn. exact 42.
  constructor.
  cbn. exact nat.
  constructor.
  cbn. exact true.
  constructor.
Qed.

(** * Predykat i relacje dla koinduktywnych pierdółek. *)

(** Zdefniuj predykat [Finite], [Infinite], [Exists], [All] dla kolist. *)
(*
Inductive Finite {A : Type} : coList A -> Prop :=
Inductive Exists {A : Type} (P : A -> Prop) : coList A -> Prop :=
*)

(** Jakieś inne. *)
(*
Inductive Finite : conat -> Prop :=

Inductive EBTree (A : Type) : nat -> Type :=
Inductive HBTree : Type :=
Inductive EHBTree : nat -> Type :=

Inductive sorted {A : Type} (R : A -> A -> Prop) : list A -> Prop :=
Inductive BHeap {A : Type} (R : A -> A -> Prop) : Type :=
Inductive BST {A : Type} (R : A -> A -> Prop) : Type :=
Inductive slist {A : Type} (R : A -> A -> bool) : Type :=
Inductive BHeap {A : Type} (R : A -> A -> bool) : Type :=

Inductive subterm_nat : nat -> nat -> Prop :=
Inductive subterm_list {A : Type} : list A -> list A -> Prop :=
Inductive subterm_nat_base : nat -> nat -> Prop :=
Inductive subterm_list_base {A : Type} : list A -> list A -> Prop :=
*)

(** Zdefiniuj różne użyteczne relacje dla strumieni, m. in. [Exists], [All],
    [Prefix], [Suffix], [Permutation] etc. *)

(*
Inductive Suffix {A : Type} : Stream A -> Stream A -> Prop :=
Inductive Permutation {A : Type} : Stream A -> Stream A -> Prop :=
*)