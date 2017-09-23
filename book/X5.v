(** * X5: Relacje *)

Require Import X4.
Require Import FunctionalExtensionality.

Require Import Nat.
Require Import List.
Import ListNotations.

(** Prerekwizyty:
    - definicje induktywne
    - klasy (?) *)

(** W tym rozdziale zajmiemy się badaniem relacji. Poznamy podstawowe rodzaje
    relacji, ich właściwości, a także zależności i przekształcenia między
    nimi. Rozdział będzie raczej matematyczny. *)

(** * Relacje *)

(** Zacznijmy od przypomnienia klasyfikacji zdań, predykatów i relacji:
    - zdania to obiekty typu [Prop]. Twierdzą one coś na temat świata:
      "niebo jest niebieskie", [P -> Q] etc. W uproszczeniu możemy myśleć o
      nich, że są prawdziwe lub fałszywe, co nie znaczy wcale, że można to
      automatycznie rozstrzygnąć. Udowodnienie zdania [P] to skonstruowanie
      obiektu [p : P]. W Coqu zdania służą nam do podawania specyfikacji
      programów. W celach klasyfikacyjnych możemy uznać, że są to funkcje
      biorące zero argumentów i zwracające [Prop].
    - predykaty to funkcje typu [A -> Prop] dla jakiegoś [A : Type]. Można
      za ich pomocą przedstawiać stwierdzenia na temat właściwości obiektów:
      "liczba 5 jest parzysta", [odd 5]. Dla niektórych argumentów zwracane
      przez nie zdania mogą być prawdziwe, a dla innych już nie. Dla celów
      klasyfikacji uznajemy je za funkcje biorące jeden argument i zwracające
      [Prop].
    - relacje to funkcje biorące dwa lub więcej argumentów, niekoniecznie
      o takich samych typach, i zwracające [Prop]. Służą one do opisywania
      zależności między obiektami, np. "Grażyna jest matką Karyny",
      [Permutation (l ++ l') (l' ++ ')]. Niektóre kombinacje obiektów mogą
      być ze sobą w relacji, tzn. zdanie zwracane dla nich przez relację
      może być prawdziwe, a dla innych nie. *)

(** Istnieje jednak zasadnicza różnica między definiowaniem "zwykłych"
    funkcji oraz definiowaniem relacji: zwykłe funkcje możemy definiować
    jedynie przez pattern matching i rekurencję, zaś relacje możemy poza
    tymi metodami definiować także przez indukcję, dzięki czemu możemy
    wyrazić więcej konceptów niż za pomocą rekursji. *)

(** **** Ćwiczenie *)

(** Funkcję Collatza klasycznie definiuje się w ten sposób: jeżeli n
    jest parzyste, to f(n) = n/2. W przeciwnym przypadku f(n) = 3n + 1.
    Zaimplementuj tę funkcję w Coqu. Zastanów się, jakiego mechanizmu
    użyć: funkcji rekurencyjnej czy relacji induktywnej?

    Udowodnij, że f(42) = 1. *)

(* begin hide *)
Inductive collatz : nat -> nat -> Prop :=
    | c_even : forall n : nat, collatz (2 * n) n
    | c_odd : forall n : nat, collatz (1 + 2 * n) (4 + 6 * n)
    | c_trans : forall a b c : nat,
        collatz a b -> collatz b c -> collatz a c.

Hint Constructors collatz.

Theorem collatz_42 : collatz 42 1.
Proof.
  apply c_trans with 21.
    change 42 with (2 * 21). constructor.
  apply c_trans with 64.
    change 21 with (1 + 2 * 10). constructor.
  apply c_trans with 2.
    Focus 2. apply (c_even 1).
  apply c_trans with 4.
    Focus 2. apply (c_even 2).
  apply c_trans with 8.
    Focus 2. apply (c_even 4).
  apply c_trans with 16.
    Focus 2. apply (c_even 8).
  apply c_trans with (32).
    Focus 2. apply (c_even 16).
  apply (c_even 32).
Qed.

Fixpoint collatz' (fuel n : nat) : list nat :=
match fuel with
    | 0 => []
    | S fuel' =>
        if leb n 1 then [n] else
            let h := if even n then div2 n else 1 + 3 * n
            in n :: collatz' fuel' h
end.

Compute map (collatz' 1000) [1; 2; 3; 4; 5; 6; 7; 8; 9].
Compute collatz' 1000 2487.
(* end hide *)

(** * Heterogeniczne relacje binarne *)

Definition hrel (A B : Type) : Type := A -> B -> Prop.

(** Najważniejszym rodzajem relacji są relacje binarne, czyli relacje
    biorące dwa argumenty. To właśnie im poświęcimy ten rozdział, pominiemy
    zaś relacje biorące trzy i więcej argumentów. Zacznijmy od zdefiniowania
    podstawowych opreacji na relacjach. *)

Definition subrelation {A B : Type} (R S : hrel A B) : Prop :=
  forall (a : A) (b : B), R a b -> S a b.

Notation "R --> S" := (subrelation R S) (at level 40).

Definition same_hrel {A B : Type} (R S : hrel A B) : Prop :=
  subrelation R S /\ subrelation S R.

Notation "R <--> S" := (same_hrel R S) (at level 40).

(** Zacznijmy od ustalenia, jakie relacje będziemy uznawać za "identyczne".
    Okazuje się, że używanie równości [eq] do porównywania zdań nie ma
    zbyt wiele sensu. Jest tak dlatego, że nie interesuje nas postać owych
    zdań, a jedynie ich logiczna zawartość.

    Z tego powodu właściwym dla zdań pojęciem "identyczności" jest
    równoważność, czyli [<->]. Podobnie jest w przypadku relacji: uznamy
    dwie relacje za identyczne, gdy dla wszystkich argumentów zwracają
    one równoważne zdania.

    Formalnie wyrazimy to nieco na około, za pomocą pojęcia subrelacji.
    [R] jest subrelacją [S], jeżeli [R a b] implikuje [S a b] dla
    wszystkich [a : A] i [b : B]. Możemy sobie wyobrażać, że jeżeli [R]
    jest subrelacją [S], to w relacji [R] są ze sobą tylko niektóre
    pary argumentów, które są w relacji [S], a inne nie. *)

(** **** Ćwiczenie *)

Inductive le' : nat -> nat -> Prop :=
    | le'_0 : forall n : nat, le' 0 n
    | le'_SS : forall n m : nat, le' n m -> le' (S n) (S m).

(** Udowodnij, że powyższa definicja [le'] porządku "mniejszy lub równy"
    na liczbach naturalnych jest tą samą relacją, co [le]. Być może
    przyda ci się kilka lematów pomocniczych. *)

(* begin hide *)
Hint Constructors le'.

Theorem le'_refl : forall n : nat, le' n n.
Proof.
  induction n as [| n']; cbn; auto.
Qed.

Theorem le'_S : forall n m : nat, le' n m -> le' n (S m).
Proof.
  induction 1; auto.
Qed.
(* end hide *)

Theorem le_le'_same : le <--> le'.
(* begin hide *)
Proof.
  split; red.
    induction 1.
      apply le'_refl.
      apply le'_S. assumption.
    induction 1.
      apply le_0_n.
      apply le_n_S. assumption.
Qed.
(* end hide *)

(** Uporawszy się z pojęciem "identyczności" relacji możemy przejść dalej,
    a mianowicie do operacji, jakie możemy wykonywać na relacjach. *)

Definition Rcomp {A B C : Type} (R : hrel A B) (S : hrel B C)
  : hrel A C := fun (a : A) (c : C) => exists b : B, R a b /\ S b c.

Definition Rid {A : Type} : hrel A A := @eq A.

(** Podobnie jak w przypadku funkcji, najważniejszą operacją jest składanie
    relacji, a najważniejszą relacją — równość. Składanie jest łączne, zaś
    równość jest elementem neutralnym tego składania. Musimy jednak zauważyć,
    że mówiąc o łączności relacji mamy na myśli coś innego, niż w przypadku
    funkcji. *)

Theorem Rcomp_assoc :
  forall (A B C D : Type) (R : hrel A B) (S : hrel B C) (T : hrel C D),
    Rcomp R (Rcomp S T) <--> Rcomp (Rcomp R S) T.
(* begin hide *)
Proof.
  unfold Rcomp. intros. split; red; intros a d **.
    decompose [ex and] H; eauto.
    decompose [ex and] H; eauto.
Qed.
(* end hide *)

Theorem Rid_left :
  forall (A B : Type) (R : hrel A B),
    Rcomp (@Rid A) R <--> R.
(* begin hide *)
Proof.
  compute; split; intros.
    decompose [ex and] H; subst; eauto.
    exists a; eauto.
Qed.
(* end hide *)

Theorem Rid_right :
  forall (A B : Type) (R : hrel A B),
    Rcomp R (@Rid B) <--> R.
(* begin hide *)
Proof.
  compute; split; intros.
    decompose [ex and] H; subst; eauto.
    exists b; eauto.
Qed.
(* end hide *)

(** Składanie funkcji jest łączne, gdyż złożenie trzech funkcji z dowolnie
    rozstawionymi nawiasami daje wynik identyczny w sensie [eq]. Składanie
    relacji jest łączne, gdyż złożenie trzech relacji z dowolnie rozstawionymi
    nawiasami daje wynik identyczny w sensie [same_hrel].

    Podobnie sprawa ma się w przypadku stwierdzenia, że [eq] jest elementem
    nautralnym składania relacji. *)

Definition Rinv {A B : Type} (R : hrel A B) : hrel B A :=
  fun (b : B) (a : A) => R a b.

Definition Rnot {A B : Type} (R : hrel A B) : hrel A B :=
  fun (a : A) (b : B) => ~ R a b.

Definition Rand {A B : Type} (R S : hrel A B) : hrel A B :=
  fun (a : A) (b : B) => R a b /\ S a b.

Definition Ror {A B : Type} (R S : hrel A B) : hrel A B :=
  fun (a : A) (b : B) => R a b \/ S a b.

Definition Rdiff {A B : Type} (R S : hrel A B) : hrel A B :=
  fun (a : A) (b : B) => R a b /\ ~ S a b.

(** A oto pozostałe operacje, jakie wykonywać możemy na funkcjach. [Rinv]
    zamienia miejscami argumenty relacji [R]. Relację [Rinv R] będziemy
    nazywać relacją odwrotną do [R].

    Pozostałe trzy operacje na relacjach odpowiadają spójnikom logicznym —
    mamy więc negację relacji oraz koniunkcję i dysjunkcję dwóch relacji.
    Zauważ, że operacje te możemy wykonywać jedynie na relacjach o takich
    samych typach argumentów.

    Sporą część naszego badania relacji przeznaczymy na sprawdzanie, jak
    powyższe operacj mają się do różnych specjalnych rodzajów relacji. Nim
    to się stanie, zbadajmy jednak właściwości samych operacji. *)

Definition RTrue {A B : Type} : hrel A B :=
  fun (a : A) (b : B) => True.

Definition RFalse {A B : Type} : hrel A B :=
  fun (a : A) (b : B) => False.

(** Zacznijmy od relacjowych odpowiedników [True] i [False]. Przydadzą się
    nam one do wyrażania właściwości [Rand] oraz [Ror]. *)

(* begin hide *)
Ltac wut :=
  unfold subrelation, same_hrel, Rcomp, Rid, Rinv, Rnot, Rand, Ror;
  repeat split; intros; firstorder.
(* end hide *)

Theorem Rnot_double :
  forall (A B : Type) (R : hrel A B),
    R --> Rnot (Rnot R).
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Theorem Rand_assoc :
  forall (A B : Type) (R S T : hrel A B),
    Rand R (Rand S T) <--> Rand (Rand R S) T.
(* begin hide *)
Proof.
  wut.
Qed.
(* end hide *)

Theorem Rand_comm :
  forall (A B : Type) (R S : hrel A B), Rand R S <--> Rand S R.
(* begin hide *)
Proof.
  wut.
Qed.
(* end hide *)

Theorem Rand_RTrue_l :
  forall (A B : Type) (R : hrel A B),
    Rand RTrue R <--> R.
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Theorem Rand_RTrue_r :
  forall (A B : Type) (R : hrel A B),
    Rand R RTrue <--> R.
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Theorem Rand_RFalse_l :
  forall (A B : Type) (R : hrel A B),
    Rand RFalse R <--> RFalse.
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Theorem Rand_RFalse_r :
  forall (A B : Type) (R : hrel A B),
    Rand R RFalse <--> RFalse.
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Theorem Ror_assoc :
  forall (A B : Type) (R S T : hrel A B),
    Ror R (Ror S T) <--> Ror (Ror R S) T.
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Theorem Ror_comm :
  forall (A B : Type) (R S : hrel A B), Ror R S <--> Ror S R.
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Theorem Ror_RTrue_l :
  forall (A B : Type) (R : hrel A B),
    Ror RTrue R <--> RTrue.
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Theorem Ror_RTrue_r :
  forall (A B : Type) (R : hrel A B),
    Ror R RTrue <--> RTrue.
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Theorem Ror_RFalse_l :
  forall (A B : Type) (R : hrel A B),
    Ror RFalse R <--> R.
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Theorem Ror_RFalse_r :
  forall (A B : Type) (R : hrel A B),
    Ror R RFalse <--> R.
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

(** To nie wszystkie właściwości tych operacji, ale myślę, że widzisz już,
    dokąd to wszystko zmierza. Jako, że [Rnot], [Rand] i [Ror] pochodzą
    bezpośrednio od spójników logicznych [not], [and] i [or], to dziedziczą
    one po nich wszystkie ich właściwości.

    Fenomen ten nie jest w żaden sposób specyficzny dla relacji i operacji
    na nich. TODO: mam nadzieję, że w przyszłych rozdziałach jeszcze się z
    nim spotkamy. Tymczasem przyjrzyjmy się bliżej specjalnym rodzajom
    relacji. *)

Class LeftUnique {A B : Type} (R : hrel A B) : Prop :=
{
    left_unique : forall (a a' : A) (b : B), R a b -> R a' b -> a = a'
}.

Class RightUnique {A B : Type} (R : hrel A B) : Prop :=
{
    right_unique : forall (a : A) (b b' : B), R a b -> R a b' -> b = b'
}.

(** Dwoma podstawowymi rodzajami relacji są relacje unikalne z lewej i prawej
    strony. Relacja lewostronnie unikalna to taka, dla której każde [b : B]
    jest w relacji z co najwyżej jednym [a : A]. Analogicznie definiujemy
    relacje prawostronnie unikalne. *)

Instance LeftUnique_eq (A : Type) : LeftUnique (@eq A).
(* begin hide *)
Proof.
  split. intros * -> ->. trivial.
Defined.
(* end hide *)

Instance RightUnique_eq (A : Type) : RightUnique (@eq A).
(* begin hide *)
Proof.
  split. intros * -> ->. trivial.
Defined.
(* end hide *)

(** Najbardziej elementarną intuicję stojącą za tymi koncepcjami można
    przedstawić na przykładzie relacji równości: jeżeli dwa obiekty są
    równe jakiemuś trzeciemu obiektowi, to muszą być także równe sobie
    nawzajem.

    Pojęcie to jest jednak bardziej ogólne i dotyczy także relacji, które
    nie są homogeniczne. W szczególności jest ono różne od pojęcia relacji
    przechodniej, które pojawi się już niedługo. *)

Instance RightUnique_Rinv
  {A B : Type} (R : hrel A B) (LU : LeftUnique R) : RightUnique (Rinv R).
(* begin hide *)
Proof.
  split. unfold Rinv; intros. apply left_unique with a; assumption.
Qed.
(* end hide *)

Instance LeftUnique_Rinv
  {A B : Type} (R : hrel A B) (RU : RightUnique R) : LeftUnique (Rinv R).
(* begin hide *)
Proof.
  split. unfold Rinv; intros. apply right_unique with b; assumption.
Qed.
(* end hide *)

(** Już na pierwszy rzut oka widać, że pojęcia te są w pewien sposób
    symetryczne. Aby uchwycić tę symetrię, możemy posłużyć się operacją
    [Rinv]. Okazuje się, że zamiana miejscami argumentów relacji lewostronnie
    unikalnej daje relację prawostronnie unikalną i vice versa. *)

(** **** Ćwiczenie *)

(** Znajdź przykład relacji, która jest lewostronnie unikalna, ale nie jest
    prawostronnie unikana.

    Znajdź przykad relacji, która jest prawostronnie unikalna, ale nie jest
    lewostronnie unikalna. *)

(* begin hide *)
Definition is_zero (b : bool) (n : nat) : Prop :=
match n with
    | 0 => b = true
    | _ => b = false
end.

Instance LeftUnique_is_zero : LeftUnique is_zero.
Proof.
  split. intros. destruct b; cbn in *; subst; trivial.
Qed.

Theorem is_zero_not_RightUnique : ~ RightUnique is_zero.
Proof.
  destruct 1. cut (1 = 2).
    inversion 1.
    apply right_unique0 with false; cbn; trivial.
Qed.

Definition is_zero' : nat -> bool -> Prop := flip is_zero.

Theorem is_zero'_not_LeftUnique : ~ LeftUnique is_zero'.
Proof.
  destruct 1. cut (1 = 2).
    inversion 1.
    apply left_unique0 with false; cbn; trivial.
Qed.

Instance RightUnique_is_zero' : RightUnique is_zero'.
Proof.
  split. destruct a; cbn; intros; subst; trivial.
Qed.
(* end hide *)

Class LeftTotal {A B : Type} (R : hrel A B) : Prop :=
{
    left_total : forall a : A, exists b : B, R a b
}.

Class RightTotal {A B : Type} (R : hrel A B) : Prop :=
{
    right_total : forall b : B, exists a : A, R a b
}.

(** Kolejnymi dwoma rodzajami heterogenicznych relacji binarnych są relacje
    lewo- i prawostronnie totalne. Relacja lewostronnie totalna to taka, że
    każde [a : A] jest w relacji z jakimś elementem [B]. Definicja relacji
    prawostronnie totalnej jest analogiczna.

    Za pojęciem tym nie stoją jakieś wielkie intuicje: relacja lewostronnie
    totalna to po prostu taka, w której żaden element [a : A] nie jest
    "osamotniony". *)

(** **** Ćwiczenie *)

(** Znajdź relację, która jest lewostronnie totalna, ale nie prawostronnie
    totalna.

    Znajdź relację, która jest prawostronnie totalna, ale nie lewostronnie
    totalna.

    Bonusowe punkty za relację, która jest "naturalna", tzn. nie została
    wymyślona na chama specjalnie na potrzeby zadania. *)

(* begin hide *)
Instance LeftTotal_lt : LeftTotal lt.
Proof.
  split. intro. exists (S a). unfold lt. apply le_n.
Qed.

Theorem lt_not_RightTotal : ~ RightTotal lt.
Proof.
  destruct 1. destruct (right_total0 0). inversion H.
Qed.

Theorem gt_not_LeftTotal : ~ LeftTotal gt.
Proof.
  destruct 1. destruct (left_total0 0). inversion H.
Qed.

Instance RightTotal_gt : RightTotal gt.
Proof.
  split. intro. exists (S b). unfold gt, lt. trivial.
Qed.
(* end hide *)






(** * Homogeniczne relacje binarne *)

Definition rel (A : Type) : Type := hrel A A.

Class Reflexive {A : Type} (R : rel A) : Prop :=
{
    reflexive : forall x : A, R x x
}.

Class Irreflexive {A : Type} (R : rel A) : Prop :=
{
    irreflexive : exists x : A, ~ R x x
}.

Class Antireflexive {A : Type} (R : rel A) : Prop :=
{
    antireflexive : forall x : A, ~ R x x
}.

Class WeakReflexive {A : Type} (R : rel A) : Prop :=
{
    wreflexive : forall x y : A, R x y -> x = y
}.

Class Symmetric {A : Type} (R : rel A) : Prop :=
{
    symmetric : forall x y : A, R x y -> R y x
}.

Class Asymmetric {A : Type} (R : rel A) : Prop :=
{
    asymmetric : exists x y : A, R x y /\ ~ R y x
}.

Class Antisymmetric {A : Type} (R : rel A) : Prop :=
{
    antisymmetric : forall x y : A, R x y -> ~ R x y
}.

Class WeakAntisymmetric {A : Type} (R : rel A) : Prop :=
{
    wantisymmetric : forall x y : A, R x y -> R y x -> x = y
}.

Class Transitive {A : Type} (R : rel A) : Prop :=
{
    transitive : forall x y z : A, R x y -> R y z -> R x z
}.

Class Total {A : Type} (R : rel A) : Prop :=
{
    total : forall x y : A, R x y \/ R y x
}.

Class Trichotomous {A : Type} (R : rel A) : Prop :=
{
    trichotomous : forall x y : A, R x y \/ x = y \/ R y x
}.
