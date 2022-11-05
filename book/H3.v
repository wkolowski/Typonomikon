(** * H3: Relacje [TODO] *)

From Typonomikon Require Import H2.
Require Import FunctionalExtensionality.

Require Import Nat.
Require Import List.
Import ListNotations.

Require Import Lia.

(* begin hide *)
(** Prerekwizyty:
    - definicje induktywne
    - klasy (?) *)

(** Do zapamiętania:
    - Semiorder      = poset z zakazanymi dwoma łańcuchami długości 2 i zakazanymi
                       dwoma łańcuchami o długościach 3 i 1
    - Interval order = poset wygenerowany z relacji porządku na odcinkach rzeczywistych,
                       czyli poset z zakazanymi dwoma łańcuchami o długości 2
    - Weak ordering  = poset, w którym nieporównywalność jest przechodnia,
                       czyli totalny preporządek,
                       czyli liniowy porządek na partycjach
    - Prewellordering = jakieś gówno bez sensu
    - Well-quasi-ordering = dobrze ufundowany preporządek bez nieskończonych antyłańcuchów.
                            Motywacja: robienie lepszych konstrukcji na preporządkach, bo
                            czasem nie zachowują one dobrego ufundowania.
    - W HoTTBooku [WellOrder] nazywa się po prostu [Ord]inal, co ma sens.
     *)

(* end hide *)

(** W tym rozdziale zajmiemy się badaniem relacji. Poznamy podstawowe rodzaje
    relacji, ich właściwości, a także zależności i przekształcenia między
    nimi. Rozdział będzie raczej matematyczny. *)

(** * Relacje binarne *)

(** Zacznijmy od przypomnienia klasyfikacji zdań, predykatów i relacji:
    - zdania to obiekty typu [Prop]. Twierdzą one coś na temat świata:
      "niebo jest niebieskie", [P -> Q] etc. W uproszczeniu możemy myśleć o
      nich, że są prawdziwe lub fałszywe, co nie znaczy wcale, że można to
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
      może być prawdziwe, a dla innych nie. *)

(** Istnieje jednak zasadnicza różnica między definiowaniem "zwykłych"
    funkcji oraz definiowaniem relacji: zwykłe funkcje możemy definiować
    jedynie przez dopasowanie do wzorca i rekurencję, zaś relacje możemy
    poza tymi metodami definiować także przez indukcję, dzięki czemu możemy
    wyrazić więcej konceptów niż za pomocą rekursji. *)

Definition hrel (A B : Type) : Type := A -> B -> Prop.

(** Najważniejszym rodzajem relacji są relacje binarne, czyli relacje
    biorące dwa argumenty. To właśnie im poświęcimy ten rozdział, pominiemy
    zaś relacje biorące trzy i więcej argumentów. Określenia "relacja binarna"
    będę używał zarówno na określenie relacji binarnych heterogenicznych
    (czyli biorących dwa argumnty różnych typów) jak i na określenie relacji
    binarnych homogenicznych (czyli biorących dwa argumenty tego samego
    typu). *)

(** * Identyczność relacji *)

Definition subrelation {A B : Type} (R S : hrel A B) : Prop :=
  forall (a : A) (b : B), R a b -> S a b.

Notation "R --> S" := (subrelation R S) (at level 40).

Definition same_hrel {A B : Type} (R S : hrel A B) : Prop :=
  subrelation R S /\ subrelation S R.

Notation "R <--> S" := (same_hrel R S) (at level 40).

(** Zacznijmy od ustalenia, jakie relacje będziemy uznawać za "identyczne".
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
    jest subrelacją [S], to w relacji [R] są ze sobą tylko niektóre
    pary argumentów, które są w relacji [S], a inne nie. *)

(** **** Ćwiczenie *)

Inductive le' : nat -> nat -> Prop :=
| le'_0 : forall n : nat, le' 0 n
| le'_SS : forall n m : nat, le' n m -> le' (S n) (S m).

(** Udowodnij, że powyższa definicja [le'] porządku "mniejszy lub równy"
    na liczbach naturalnych jest tą samą relacją, co [le]. Być może
    przyda ci się kilka lematów pomocniczych. *)

(* begin hide *)
#[global] Hint Constructors le' : core.

Lemma le'_refl : forall n : nat, le' n n.
Proof.
  induction n as [| n']; cbn; auto.
Qed.

Lemma le'_S : forall n m : nat, le' n m -> le' n (S m).
Proof.
  induction 1; auto.
Qed.
(* end hide *)

Lemma le_le'_same : le <--> le'.
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

(** Uporawszy się z pojęciem "identyczności" relacji możemy przejść dalej,
    a mianowicie do operacji, jakie możemy wykonywać na relacjach. *)

(** * Operacje na relacjach *)

Definition Rcomp
  {A B C : Type} (R : hrel A B) (S : hrel B C) : hrel A C :=
    fun (a : A) (c : C) => exists b : B, R a b /\ S b c.

Definition Rid {A : Type} : hrel A A := @eq A.

(** Podobnie jak w przypadku funkcji, najważniejszą operacją jest składanie
    relacji, a najważniejszą relacją — równość. Składanie jest łączne, zaś
    równość jest elementem neutralnym tego składania. Musimy jednak zauważyć,
    że mówiąc o łączności relacji mamy na myśli coś innego, niż w przypadku
    funkcji. *)

Lemma Rcomp_assoc :
  forall
    (A B C D : Type) (R : hrel A B) (S : hrel B C) (T : hrel C D),
      Rcomp R (Rcomp S T) <--> Rcomp (Rcomp R S) T.
(* begin hide *)
Proof.
  unfold Rcomp. intros. split; red; intros a d **.
    decompose [ex and] H; eauto.
    decompose [ex and] H; eauto.
Qed.
(* end hide *)

Lemma Rcomp_eq_l :
  forall (A B : Type) (R : hrel A B),
    Rcomp (@Rid A) R <--> R.
(* begin hide *)
Proof.
  compute; split; intros.
  - decompose [ex and] H; subst; eauto.
  - exists a; eauto.
Qed.
(* end hide *)

Lemma Rcomp_eq_r :
  forall (A B : Type) (R : hrel A B),
    Rcomp R (@Rid B) <--> R.
(* begin hide *)
Proof.
  compute; split; intros.
  - decompose [ex and] H; subst; eauto.
  - exists b; eauto.
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

(** [Rinv] to operacja, która zamienia miejscami argumenty relacji. Relację
    [Rinv R] będziemy nazywać relacją odwrotną do [R]. *)

Lemma Rinv_Rcomp :
  forall (A B C : Type) (R : hrel A B) (S : hrel B C),
    Rinv (Rcomp R S) <--> Rcomp (Rinv S) (Rinv R).
(* begin hide *)
Proof.
  compute; split; intros; firstorder.
Qed.
(* end hide *)

Lemma Rinv_eq :
  forall A : Type, Rinv (@Rid A) <--> @Rid A.
(* begin hide *)
Proof. compute. firstorder. Qed.
(* end hide *)

(** Złożenie dwóch relacji możemy odwrócić, składając ich odwrotności w
    odwrotnej kolejności. Odwrotnością relacji identycznościowej jest
    zaś ona sama. *)

Definition Rnot {A B : Type} (R : hrel A B) : hrel A B :=
  fun (a : A) (b : B) => ~ R a b.

Definition Rand {A B : Type} (R S : hrel A B) : hrel A B :=
  fun (a : A) (b : B) => R a b /\ S a b.

Definition Ror {A B : Type} (R S : hrel A B) : hrel A B :=
  fun (a : A) (b : B) => R a b \/ S a b.

(** Pozostałe trzy operacje na relacjach odpowiadają spójnikom logicznym —
    mamy więc negację relacji oraz koniunkcję i dysjunkcję dwóch relacji.
    Zauważ, że operacje te możemy wykonywać jedynie na relacjach o takich
    samych typach argumentów.

    Sporą część naszego badania relacji przeznaczymy na sprawdzanie, jak
    powyższe operacj mają się do różnych specjalnych rodzajów relacji. Nim
    to się stanie, zbadajmy jednak właściwości samych operacji. *)

Definition RTrue {A B : Type} : hrel A B :=
  fun (a : A) (b : B) => True.

Definition RFalse {A B : Type} : hrel A B :=
  fun (a : A) (b : B) => False.

(** Zacznijmy od relacjowych odpowiedników [True] i [False]. Przydadzą się
    nam one do wyrażania właściwości [Rand] oraz [Ror]. *)

(* begin hide *)
Ltac rel :=
  unfold
    subrelation, same_hrel, Rcomp, Rid, Rinv, Rnot, Rand, Ror, RTrue, RFalse;
  compute; repeat split; intros; firstorder; subst; eauto;
repeat match goal with
| H : False |- _ => destruct H
| x : Empty_set |- _ => destruct x
| H : True  |- _ => destruct H
| x : unit  |- _ => destruct x
end; try congruence.
(* end hide *)

Lemma Rnot_Rnot :
  forall (A B : Type) (R : hrel A B),
    R --> Rnot (Rnot R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma Rand_assoc :
  forall (A B : Type) (R S T : hrel A B),
    Rand R (Rand S T) <--> Rand (Rand R S) T.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma Rand_comm :
  forall (A B : Type) (R S : hrel A B),
    Rand R S <--> Rand S R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma Rand_RTrue_l :
  forall (A B : Type) (R : hrel A B),
    Rand RTrue R <--> R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma Rand_RTrue_r :
  forall (A B : Type) (R : hrel A B),
    Rand R RTrue <--> R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma Rand_RFalse_l :
  forall (A B : Type) (R : hrel A B),
    Rand RFalse R <--> RFalse.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma Rand_RFalse_r :
  forall (A B : Type) (R : hrel A B),
    Rand R RFalse <--> RFalse.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma Ror_assoc :
  forall (A B : Type) (R S T : hrel A B),
    Ror R (Ror S T) <--> Ror (Ror R S) T.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma Ror_comm :
  forall (A B : Type) (R S : hrel A B),
    Ror R S <--> Ror S R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma Ror_RTrue_l :
  forall (A B : Type) (R : hrel A B),
    Ror RTrue R <--> RTrue.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma Ror_RTrue_r :
  forall (A B : Type) (R : hrel A B),
    Ror R RTrue <--> RTrue.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma Ror_RFalse_l :
  forall (A B : Type) (R : hrel A B),
    Ror RFalse R <--> R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma Ror_RFalse_r :
  forall (A B : Type) (R : hrel A B),
    Ror R RFalse <--> R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** To nie wszystkie właściwości tych operacji, ale myślę, że widzisz już,
    dokąd to wszystko zmierza. Jako, że [Rnot], [Rand] i [Ror] pochodzą
    bezpośrednio od spójników logicznych [not], [and] i [or], dziedziczą
    one po nich wszystkie ich właściwości.

    Fenomen ten nie jest w żaden sposób specyficzny dla relacji i operacji
    na nich - z pewnością spotkamy się z nim ponownie w nadchodzących
    rozdziałach. Tymczasem przyjrzyjmy się bliżej specjalnym rodzajom
    relacji. *)

(** * Rodzaje relacji heterogenicznych *)

(** ** Relacje lewo- i prawostronnie unikalne *)

(* begin hide *)
(* TODO: napisać, że lepszą nazwą dla [RightUnique] jest "relacja deterministyczna". *)
(* end hide *)

Class LeftUnique {A B : Type} (R : hrel A B) : Prop :=
{
    left_unique :
      forall (a a' : A) (b : B), R a b -> R a' b -> a = a'
}.

Class RightUnique {A B : Type} (R : hrel A B) : Prop :=
{
    right_unique :
      forall (a : A) (b b' : B), R a b -> R a b' -> b = b'
}.

(** Dwoma podstawowymi rodzajami relacji są relacje unikalne z lewej i prawej
    strony. Relacja lewostronnie unikalna to taka, dla której każde [b : B]
    jest w relacji z co najwyżej jednym [a : A]. Analogicznie definiujemy
    relację prawostronnie unikalną. *)

#[export]
Instance LeftUnique_eq (A : Type) : LeftUnique (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance RightUnique_eq (A : Type) : RightUnique (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Najbardziej elementarną intuicję stojącą za tymi koncepcjami można
    przedstawić na przykładzie relacji równości: jeżeli dwa obiekty są
    równe jakiemuś trzeciemu obiektowi, to muszą być także równe sobie
    nawzajem.

    Pojęcie to jest jednak bardziej ogólne i dotyczy także relacji, które
    nie są homogeniczne. W szczególności jest ono różne od pojęcia relacji
    przechodniej, które pojawi się już niedługo. *)

#[export]
Instance LeftUnique_Rcomp :
  forall (A B C : Type) (R : hrel A B) (S : hrel B C),
    LeftUnique R -> LeftUnique S -> LeftUnique (Rcomp R S).
(* begin hide *)
Proof.
  rel. specialize (left_unique0 _ _ _ H0 H2). subst.
  apply left_unique1 with x0; assumption.
Qed.
(* end hide *)

#[export]
Instance RightUnique_Rcomp :
  forall (A B C : Type) (R : hrel A B) (S : hrel B C),
    RightUnique R -> RightUnique S -> RightUnique (Rcomp R S).
(* begin hide *)
Proof.
  rel. specialize (right_unique1 _ _ _ H H1). subst.
  apply right_unique0 with x0; assumption.
Qed.
(* end hide *)

(** Składanie zachowuje oba rodzaje relacji unikalnych. Nie ma tu co
    za dużo filozofować — żeby się przekonać, narysuj obrazek. TODO. *)

#[export]
Instance LeftUnique_Rinv :
  forall (A B : Type) (R : hrel A B),
    RightUnique R -> LeftUnique (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance RightUnique_Rinv :
  forall (A B : Type) (R : hrel A B),
    LeftUnique R -> RightUnique (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Już na pierwszy rzut oka widać, że pojęcia te są w pewien sposób
    symetryczne. Aby uchwycić tę symetrię, możemy posłużyć się operacją
    [Rinv]. Okazuje się, że zamiana miejscami argumentów relacji lewostronnie
    unikalnej daje relację prawostronnie unikalną i vice versa. *)

#[export]
Instance LeftUnique_Rand :
  forall (A B : Type) (R S : hrel A B),
    LeftUnique R -> LeftUnique (Rand R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance RightUnique_Rand :
  forall (A B : Type) (R S : hrel A B),
    RightUnique R -> RightUnique (Rand R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_LeftUnique_Ror :
  exists (A B : Type) (R S : hrel A B),
    LeftUnique R /\ LeftUnique S /\ ~ LeftUnique (Ror R S).
(* begin hide *)
Proof.
  exists bool, bool, (@eq bool), (fun b b' => b = negb b').
  rel. specialize (left_unique0 true false true).
  contradict left_unique0. intuition.
Qed.
(* end hide *)

Lemma not_RightUnique_Ror :
  exists (A B : Type) (R S : hrel A B),
    RightUnique R /\ RightUnique S /\ ~ RightUnique (Ror R S).
(* begin hide *)
Proof.
  exists bool, bool, (fun b b' => b = negb b'), (@eq bool).
  rel.
  - destruct b, b'; intuition.
  - specialize (right_unique0 true false true).
    contradict right_unique0. intuition.
Qed.
(* end hide *)

(** Koniunkcja relacji unikalnej z inną daje relację unikalną, ale dysjunkcja
    nawet dwóch relacji unikalnych nie musi dawać w wyniku relacji unikalnej.
    Wynika to z interpretacji operacji na relacjach jako operacji na
    kolekcjach par.

    Wyobraźmy sobie, że relacja [R : hrel A B] to kolekcja par [p : A * B].
    Jeżeli para jest elementem kolekcji, to jej pierwszy komponent jest w
    relacji [R] z jej drugim komponentem. Dysjunkcję relacji [R] i [S] w
    takim układzie stanowi kolekcja, która zawiera zarówno pary z kolekcji
    odpowiadającej [R], jak i te z kolekcji odpowiadającej [S]. Koniunkcja
    odpowiada kolekcji par, które są zarówno w kolekcji odpowiadającej [R],
    jak i tej odpowiadającej [S].

    Tak więc dysjunkcja [R] i [S] może do [R] "dorzucić" jakieś pary, ale
    nie może ich zabrać. Analogicznie, koniunkcja [R] i [S] może zabrać
    pary z [R], ale nie może ich dodać.

    Teraz interpretacja naszego wyniku jest prosta. W przypadku relacji
    lewostronnie unikalnych jeżeli każde [b : B] jest w relacji z co
    najwyżej jednym [a : A], to potencjalne zabranie jakichś par z tej
    relacji niczego nie zmieni. Z drugiej strony, nawet jeżeli obie relacje
    są lewostronnie unikalne, to dodanie do [R] par z [S] może spowodować
    wystąpienie powtórzeń, co niszczy unikalność. *)

Lemma not_LeftUnique_Rnot :
  exists (A B : Type) (R : hrel A B),
    LeftUnique R /\ ~ LeftUnique (Rnot R).
(* begin hide *)
Proof.
  pose (R := @eq (option bool)).
  exists (option bool), (option bool), R.
  rel. cut (Some true = Some false).
    inversion 1.
    apply left_unique0 with None; inversion 1.
Qed.
(* end hide *)

Lemma not_RightUnique_Rnot :
  exists (A B : Type) (R : hrel A B),
    LeftUnique R /\ ~ LeftUnique (Rnot R).
(* begin hide *)
Proof.
  pose (R := @eq (option bool)).
  exists (option bool), (option bool), R.
  rel. cut (Some true = Some false).
    inversion 1.
    apply left_unique0 with None; inversion 1.
Qed.
(* end hide *)

(** Negacja relacji unikalnej również nie musi być unikalna. Spróbuj podać
    interpretację tego wyniku z punktu widzenia operacji na kolekcjach par. *)

(** **** Ćwiczenie *)

(** Znajdź przykład relacji, która:
    - nie jest unikalna ani lewostronnie, ani prawostronnie
    - jest unikalna lewostronnie, ale nie prawostronnie
    - jest unikalna prawostronnie, ale nie nie lewostronnie
    - jest obustronnie unikalna *)

(* begin hide *)
Definition Rnegb (b b' : bool) : Prop := b = negb b'.

Definition NRL (b b' : bool) : Prop :=
  if b then b = negb b' else False.

Lemma not_LeftUnique_RTrue_bool :
  ~ LeftUnique (@RTrue bool bool).
Proof.
  compute. destruct 1. cut (true = false).
  - inversion 1.
  - rel.
Qed.

Lemma not_RightUnique_RTrue_bool :
  ~ RightUnique (@RTrue bool bool).
Proof.
  compute. destruct 1. cut (true = false).
  - inversion 1.
  - rel.
Qed.

Definition is_zero (b : bool) (n : nat) : Prop :=
match n with
| 0 => b = true
| _ => b = false
end.

#[export]
Instance LeftUnique_is_zero : LeftUnique is_zero.
Proof.
  split. intros. destruct b; cbn in *; subst; trivial.
Qed.

Lemma not_RightUnique_is_zero : ~ RightUnique is_zero.
Proof.
  destruct 1. cut (1 = 2).
    inversion 1.
    apply right_unique0 with false; cbn; trivial.
Qed.

Definition is_zero' : nat -> bool -> Prop := Rinv is_zero.

Lemma not_LeftUnique_is_zero' : ~ LeftUnique is_zero'.
Proof.
  destruct 1. cut (1 = 2).
    inversion 1.
    apply left_unique0 with false; cbn; trivial.
Qed.

#[export]
Instance RightUnique_is_zero' : RightUnique is_zero'.
Proof.
  split. destruct a; cbn; intros; subst; trivial.
Qed.

#[export]
Instance LeftUnique_RFalse :
  forall A B : Type, LeftUnique (@RFalse A B).
Proof. rel. Qed.

#[export]
Instance RightUnique_RFalse :
  forall A B : Type, RightUnique (@RFalse A B).
Proof. rel. Qed.
(* end hide *)

(** ** Relacje lewo- i prawostronnie totalne *)

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

    Za pojęciem tym nie stoją jakieś wielkie intuicje: relacja lewostronnie
    totalna to po prostu taka, w której żaden element [a : A] nie jest
    "osamotniony". *)

#[export]
Instance LeftTotal_RTrue :
  forall A : Type, LeftTotal (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance RightTotal_RTrue :
  forall A : Type, RightTotal (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** TODO *)

#[export]
Instance LeftTotal_RFalse_Empty :
  LeftTotal (@RFalse Empty_set Empty_set).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance RightTotal_RFalse_Empty :
  RightTotal (@RFalse Empty_set Empty_set).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_LeftTotal_RFalse_inhabited :
  forall A B : Type,
    A -> ~ LeftTotal (@RFalse A B).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_RightTotal_RFalse_inhabited :
  forall A B : Type,
    B -> ~ RightTotal (@RFalse A B).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** TODO *)

#[export]
Instance LeftTotal_eq :
  forall A : Type, LeftTotal (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance RightTotal_eq :
  forall A : Type, RightTotal (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Równość jest relacją totalną, gdyż każdy term [x : A] jest równy samemu
    sobie. *)

#[export]
Instance LeftTotal_Rcomp :
  forall (A B C : Type) (R : hrel A B) (S : hrel B C),
    LeftTotal R -> LeftTotal S -> LeftTotal (Rcomp R S).
(* begin hide *)
Proof.
  intros A B C R S [LTR] [LTS].
  split; compute; intros a.
  destruct (LTR a) as [b r],
           (LTS b) as [c s].
  exists c, b. split; assumption.
Qed.
(* end hide *)

#[export]
Instance RightTotal_Rcomp :
  forall (A B C : Type) (R : hrel A B) (S : hrel B C),
    RightTotal R -> RightTotal S -> RightTotal (Rcomp R S).
(* begin hide *)
Proof.
  rel. rename b into c.
  destruct (right_total0 c) as [b H].
  destruct (right_total1 b) as [a H'].
  exists a, b. split; assumption.
Qed.
(* end hide *)

#[export]
Instance RightTotal_Rinv :
  forall (A B : Type) (R : hrel A B),
    LeftTotal R -> RightTotal (Rinv R).
(* begin hide *)
Proof.
  unfold Rinv; split. intro a. destruct H.
  destruct (left_total0 a) as [b H]. exists b. assumption.
Qed.
(* end hide *)

#[export]
Instance LeftTotal_Rinv :
  forall (A B : Type) (R : hrel A B),
    RightTotal R -> LeftTotal (Rinv R).
(* begin hide *)
Proof.
  unfold Rinv; split. intro a. destruct H.
  destruct (right_total0 a) as [b H]. exists b. assumption.
Qed.
(* end hide *)

(** Między lewo- i prawostronną totalnością występuje podobna symetria jak
    między dwoma formami unikalności: relacja odwrotna do lewostronnie
    totalnej jest prawostronnie totalna i vice versa. Totalność jest również
    zachowywana przez składanie. *)

Lemma not_LeftTotal_Rnot :
  exists (A B : Type) (R : hrel A B),
    RightTotal R /\ ~ RightTotal (Rnot R).
(* begin hide *)
Proof.
  exists unit, unit, (@eq unit). rel.
  destruct (right_total0 tt), x. apply H. trivial.
Qed.
(* end hide *)

Lemma not_RightTotal_Rnot :
  exists (A B : Type) (R : hrel A B),
    RightTotal R /\ ~ RightTotal (Rnot R).
(* begin hide *)
Proof.
  exists unit, unit, (@eq unit). rel.
  destruct (right_total0 tt), x. apply H. trivial.
Qed.
(* end hide *)

(** Negacja relacji totalnej nie może być totalna. Nie ma się co dziwić —
    negacja wyrzuca z relacji wszystkie pary, których w niej nie było, a
    więc pozbywa się czynnika odpowiedzialnego za totalność. *)

Lemma not_LeftTotal_Rand :
  exists (A B : Type) (R S : hrel A B),
    LeftTotal R /\ LeftTotal S /\ ~ LeftTotal (Rand R S).
(* begin hide *)
Proof.
  exists bool, bool.
  exists (@Rid bool), (fun b b' => b = negb b').
  rel.
    exists (negb a). destruct a; trivial.
    destruct (left_total0 true).
      destruct x, H; cbn in H0; try congruence.
Qed.
(* end hide *)

Lemma not_RightTotal_Rand :
  exists (A B : Type) (R S : hrel A B),
    RightTotal R /\ RightTotal S /\ ~ RightTotal (Rand R S).
(* begin hide *)
Proof.
  exists bool, bool.
  exists (@Rid bool), (fun b b' => b = negb b').
  rel. destruct (right_total0 true).
  destruct x, H; cbn in H0; try congruence.
Qed.
(* end hide *)

Lemma LeftTotal_Ror :
  forall (A B : Type) (R S : hrel A B),
    LeftTotal R -> LeftTotal (Ror R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma RightTotal_Ror :
  forall (A B : Type) (R S : hrel A B),
    RightTotal R -> RightTotal (Ror R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Związki totalności z koniunkcją i dysjunkcją relacji są podobne jak
    w przypadku unikalności, lecz tym razem to dysjunkcja zachowuje
    właściwość, a koniunkcja ją niszczy. Wynika to z tego, że dysjunkcja
    nie zabiera żadnych par z relacji, więc nie może uszkodzić totalności.
    Z drugiej strony koniunkcja może zabrać jakąś parę, a wtedy relacja
    przestaje być totalna. *)

(** **** Ćwiczenie *)

(** Znajdź przykład relacji, która:
    - nie jest totalna ani lewostronnie, ani prawostronnie
    - jest totalna lewostronnie, ale nie prawostronnie
    - jest totalna prawostronnie, ale nie nie lewostronnie
    - jest obustronnie totalna *)

(** Bonusowe punkty za relację, która jest "naturalna", tzn. nie została
    wymyślona na chama specjalnie na potrzeby zadania. *)

(* begin hide *)
Lemma not_LeftTotal_RFalse_inhabited' :
  forall A B : Type, A -> ~ LeftTotal (@RFalse A B).
Proof. rel. Qed.

Lemma not_RightTotal_RFalse_inhabited' :
  forall A B : Type, B -> ~ RightTotal (@RFalse A B).
Proof. rel. Qed.

#[export]
Instance LeftTotal_lt : LeftTotal lt.
Proof.
  split. intro. exists (S a). unfold lt. apply le_n.
Qed.

Lemma not_RightTotal_lt : ~ RightTotal lt.
Proof.
  destruct 1. destruct (right_total0 0). inversion H.
Qed.

Lemma not_LeftTotal_gt : ~ LeftTotal gt.
Proof.
  destruct 1. destruct (left_total0 0). inversion H.
Qed.

#[export]
Instance RightTotal_gt : RightTotal gt.
Proof.
  split. intro. exists (S b). unfold gt, lt. trivial.
Qed.

#[export]
Instance LeftTotal_RTrue_inhabited :
  forall A B : Type, B -> LeftTotal (@RTrue A B).
Proof. rel. Qed.

#[export]
Instance RightTotal_RTrue_inhabited :
  forall A B : Type, A -> RightTotal (@RTrue A B).
Proof. rel. Qed.
(* end hide *)

(** * Rodzaje relacji heterogenicznych v2 *)

(** Poznawszy cztery właściwości, jakie relacje mogą posiadać, rozważymy
    teraz relacje, które posiadają dwie lub więcej z tych właściwości. *)

(** ** Relacje funkcyjne *)

Class Functional {A B : Type} (R : hrel A B) : Prop :=
{
    F_LT :> LeftTotal R;
    F_RU :> RightUnique R;
}.

(** Lewostronną totalność i prawostronną unikalność możemy połączyć, by
    uzyskać pojęcie relacji funkcyjnej. Relacja funkcyjna to relacja,
    która ma właściwości takie, jak funkcje — każdy lewostronny argument
    [a : A] jest w relacji z dokładnie jednym [b : B] po prawej stronie. *)

#[export]
Instance fun_to_Functional {A B : Type} (f : A -> B)
  : Functional (fun (a : A) (b : B) => f a = b).
(* begin hide *)
Proof.
  repeat split; intros.
  - exists (f a). trivial.
  - subst. trivial.
Qed.
(* end hide *)

(* begin hide *)
Definition Functional_to_fun
  {A B : Type} (R : hrel A B) (F : Functional R) : A -> B.
Proof.
  intro a. destruct F as [[LT] [RU]].
  specialize (LT a).
  Require Import IndefiniteDescription. (* TODO *)
  apply constructive_indefinite_description in LT.
  destruct LT as [b _]. exact b.
Qed.
(* end hide *)

(** Z każdej funkcji można w prosty sposób zrobić relację funkcyjną, ale
    bez dodatkowych aksjomatów nie jesteśmy w stanie z relacji funkcyjnej
    zrobić funkcji. Przemilczając kwestie aksjomatów możemy powiedzieć
    więc, że relacje funkcyjne odpowiadają funkcjom. *)

#[export]
Instance Functional_eq :
  forall A : Type, Functional (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Równość jest rzecz jasna relacją funkcyjną. Funkcją odpowiadającą
    relacji [@eq A] jest funkcja identycznościowa [@id A]. *)

#[export]
Instance Functional_Rcomp :
  forall (A B C : Type) (R : hrel A B) (S : hrel B C),
    Functional R -> Functional S -> Functional (Rcomp R S).
(* begin hide *)
Proof.
  destruct 1, 1; split.
    apply LeftTotal_Rcomp; assumption.
    apply RightUnique_Rcomp; assumption.
Qed.
(* end hide *)

(** Złożenie relacji funkcyjnych również jest relacją funkcyjną. Nie powinno
    nas to dziwić — wszakże relacje funkcyjne odpowiadają funkcjom, a złożenie
    funkcji jest przecież funkcją. Jeżeli lepiej mu się przyjrzeć, to okazuje
    się, że składanie funkcji odpowiada składaniu relacji, a stąd już prosta
    droga do wniosku, że złożenie relacji funkcyjnych jest relacją funkcyjną.
*)

Lemma not_Functional_Rinv :
  exists (A B : Type) (R : hrel A B),
    Functional R /\ ~ Functional (Rinv R).
(* begin hide *)
Proof.
  exists bool, bool, (fun b b' => b' = true).
  split.
  - rel.
  - destruct 1. destruct F_LT0. destruct (left_total0 false) as [b H].
    destruct b; inversion H.
Qed.
(* end hide *)

(** Odwrotność relacji funkcyjnej nie musi być funkcyjna. Dobrą wizualicją
    tego faktu może być np. funkcja f(x) = x^2 na liczbach rzeczywistych.
    Z pewnością jest to funkcja, a zatem relacja funkcyjna. Widać to na jej
    wykresie — każdemu punktowi dziedziny odpowiada dokładnie jeden punkt
    przeciwdziedziny. Jednak po wykonaniu operacji [Rinv], której odpowiada
    tutaj obrócenie układu współrzędnych o 90 stopni, nie otrzymujemy wcale
    wykresu funkcji. Wprost przeciwnie — niektórym punktom z osi X na takim
    wykresie odpowiadają dwa punkty na osi Y (np. punktowi 4 odpowiadają 2
    i -2). Stąd wnioskujemy, że odwrócenie relacji funkcyjnej f nie daje w
    wyniku relacji funkcyjnej. *)

Lemma not_Functional_Rand :
  exists (A B : Type) (R S : hrel A B),
    Functional R /\ Functional S /\ ~ Functional (Rand R S).
(* begin hide *)
Proof.
  exists bool, bool.
  exists (@Rid bool), (fun b b' => b = negb b').
  rel.
    exists (negb a). destruct a; trivial.
    destruct b, b'; cbn in H0; congruence.
    destruct (left_total0 true), x, H; cbn in H0; congruence.
Qed.
(* end hide *)

Lemma not_Functional_Ror :
  exists (A B : Type) (R S : hrel A B),
    Functional R /\ Functional S /\ ~ Functional (Ror R S).
(* begin hide *)
Proof.
  exists bool, bool.
  exists (@Rid bool), (fun b b' => b = negb b').
  rel.
    exists (negb a). destruct a; trivial.
    destruct b, b'; cbn in H0; congruence.
    cut (false = true).
      inversion 1.
      apply right_unique0 with false; auto.
Qed.
(* end hide *)

Lemma not_Functional_Rnot :
  exists (A B : Type) (R : hrel A B),
    Functional R /\ ~ Functional (Rnot R).
(* begin hide *)
Proof.
  pose (A := option bool).
  exists A, A, (@eq A). rel.
  cut (Some true = Some false).
    inversion 1.
    apply right_unique0 with None; inversion 1.
Qed.
(* end hide *)

(** Ani koniunkcje, ani dysjunkcje, ani negacje relacji funkcyjnych nie
    muszą być wcale relacjami funkcyjnymi. Jest to po części konsekwencją
    właściwości relacji lewostronnie totalnych i prawostronnie unikalnych:
    pierwsze mają problem z [Rand], a drugie z [Ror], oba zaś z [Rnot]. *)

(** **** Ćwiczenie *)

(** Możesz zadawać sobie pytanie: po co nam w ogóle pojęcie relacji
    funkcyjnej, skoro mamy funkcje? Funkcje muszą być obliczalne (ang.
    computable) i to na mocy definicji, zaś relacje — niekonieczne.
    Czasem prościej może być najpierw zdefiniować relację, a dopiero
    później pokazać, że jest funkcyjna. Czasem zdefiniowanie danego
    bytu jako funkcji może być niemożliwe.

    Funkcję Collatza klasycznie definiuje się w ten sposób: jeżeli n
    jest parzyste, to f(n) = n/2. W przeciwnym przypadku f(n) = 3n + 1.

    Zaimplementuj tę funkcję w Coqu. Spróbuj zaimplementować ją zarówno
    jako funkcję rekurencyjną, jak i relację. Czy twoja funkcja dokładnie
    odpowiada powyższej specyfikacji? Czy jesteś w stanie pokazać, że twoja
    relacja jest funkcyjna?

    Udowodnij, że f(42) = 1. *)

(* begin hide *)
Fixpoint collatz' (fuel n : nat) : list nat :=
match fuel with
| 0 => []
| S fuel' =>
  if leb n 1 then [n] else
      let h := if even n then div2 n else 1 + 3 * n
      in n :: collatz' fuel' h
end.

(*
Compute map (collatz' 1000) [1; 2; 3; 4; 5; 6; 7; 8; 9].
Compute collatz' 1000 2487.
*)

Inductive collatz : nat -> nat -> Prop :=
| c_even : forall n : nat, collatz (2 * n) n
| c_odd : forall n : nat, collatz (1 + 2 * n) (4 + 6 * n)
| c_trans :
    forall a b c : nat,
      collatz a b -> collatz b c -> collatz a c.

#[global] Hint Constructors collatz : core.

Lemma collatz_42 : collatz 42 1.
Proof.
  apply c_trans with 21.
    change 42 with (2 * 21). constructor.
  apply c_trans with 64.
    change 21 with (1 + 2 * 10). constructor.
  apply c_trans with 2.
    2: apply (c_even 1).
  apply c_trans with 4.
    2: apply (c_even 2).
  apply c_trans with 8.
    2: apply (c_even 4).
  apply c_trans with 16.
    2: apply (c_even 8).
  apply c_trans with (32).
    2: apply (c_even 16).
  apply (c_even 32).
Qed.
(* end hide *)

(** ** Relacje injektywne *)

Class Injective {A B : Type} (R : hrel A B) : Prop :=
{
    I_Fun :> Functional R;
    I_LU :> LeftUnique R;
}.

#[export]
Instance inj_to_Injective :
  forall (A B : Type) (f : A -> B),
    injective f -> Injective (fun (a : A) (b : B) => f a = b).
(* begin hide *)
Proof.
  split.
    apply fun_to_Functional.
    rel.
Qed.
(* end hide *)

(** Relacje funkcyjne, które są lewostronnie unikalne, odpowiadają funkcjom
    injektywnym. *)

#[export]
Instance Injective_eq :
  forall A : Type, Injective (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Injective_Rcomp :
  forall (A B C : Type) (R : hrel A B) (S : hrel B C),
    Injective R -> Injective S -> Injective (Rcomp R S).
(* begin hide *)
Proof.
  split; destruct H, H0.
    apply Functional_Rcomp; assumption.
    apply LeftUnique_Rcomp; assumption.
Qed.
(* end hide *)

Lemma not_Injective_Rinv :
  exists (A B : Type) (R : hrel A B),
    Injective R /\ ~ Injective (Rinv R).
(* begin hide *)
Proof.
  exists bool, (option bool),
  (fun (b : bool) (ob : option bool) => Some b = ob).
  rel.
    destruct (left_total0 None) as [b H]. inversion H.
Qed.
(* end hide *)

Lemma not_Injective_Rand :
  exists (A B : Type) (R S : hrel A B),
    Injective R /\ Injective S /\ ~ Injective (Rand R S).
(* begin hide *)
Proof.
  exists bool, bool.
  exists (@Rid bool), (fun b b' => b = negb b').
  rel.
    exists (negb a). destruct a; trivial.
    destruct b, b'; cbn in H0; congruence.
    destruct (left_total0 true). destruct x, H; cbn in H0; congruence.
Qed.
(* end hide *)

Lemma not_Injective_Ror :
  exists (A B : Type) (R S : hrel A B),
    Injective R /\ Injective S /\ ~ Injective (Ror R S).
(* begin hide *)
Proof.
  exists bool, bool.
  exists (@Rid bool), (fun b b' => b = negb b').
  rel.
    exists (negb a). destruct a; trivial.
    destruct b, b'; cbn in H0; congruence.
    cut (false = true).
      inversion 1.
      apply right_unique0 with false; auto.
Qed.
(* end hide *)

Lemma not_Injective_Rnot :
  exists (A B : Type) (R : hrel A B),
    Injective R /\ ~ Injective (Rnot R).
(* begin hide *)
Proof.
  pose (A := option bool).
  exists A, A, (@eq A).
  rel. cut (Some true = Some false).
    inversion 1.
    apply right_unique0 with None; inversion 1.
Qed.
(* end hide *)

(** Właściwości relacji injektywnych są takie, jak funkcji injektywnych,
    gdyż te pojęcia ściśle sobie odpowiadają. *)

(** **** Ćwiczenie *)

(** Udowodnij, że powyższe zdanie nie kłamie. *)

Lemma injective_Injective :
  forall (A B : Type) (f : A -> B),
    injective f <-> Injective (fun (a : A) (b : B) => f a = b).
(* begin hide *)
Proof.
  split.
    compute; intros. repeat split; intros.
      exists (f a). reflexivity.
      rewrite <- H0, <- H1. reflexivity.
      apply H. rewrite H0, H1. reflexivity.
    destruct 1 as [[[] []] []]. red. intros.
      apply left_unique0 with (f x').
        assumption.
        reflexivity.
Qed.
(* end hide *)

(** ** Relacje surjektywne *)

Class Surjective {A B : Type} (R : hrel A B) : Prop :=
{
    S_Fun :> Functional R;
    S_RT :> RightTotal R;
}.

#[export]
Instance sur_to_Surjective :
  forall (A B : Type) (f : A -> B),
    surjective f -> Surjective (fun (a : A) (b : B) => f a = b).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Relacje funkcyjne, które są prawostronnie totalne, odpowiadają funkcjom
    surjektywnym. *)

#[export]
Instance Surjective_eq :
  forall A : Type, Surjective (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Surjective_Rcomp :
  forall (A B C : Type) (R : hrel A B) (S : hrel B C),
    Surjective R -> Surjective S -> Surjective (Rcomp R S).
(* begin hide *)
Proof.
  split; destruct H, H0.
    apply Functional_Rcomp; assumption.
    apply RightTotal_Rcomp; assumption.
Qed.
(* end hide *)

Lemma not_Surjective_Rinv :
  exists (A B : Type) (R : hrel A B),
    Surjective R /\ ~ Surjective (Rinv R).
(* begin hide *)
Proof.
  exists (option bool), bool,
  (fun (ob : option bool) (b : bool) =>
  match ob with
  | None => b = true
  | Some _ => ob = Some b
  end).
  rel.
    destruct a; eauto.
    destruct a, b, b'; congruence.
    exists (Some b). trivial.
    cut (None = Some true).
      inversion 1.
      apply right_unique0 with true; auto.
Qed.
(* end hide *)

Lemma not_Surjective_Rand :
  exists (A B : Type) (R S : hrel A B),
    Surjective R /\ Surjective S /\ ~ Surjective (Rand R S).
(* begin hide *)
Proof.
  exists bool, bool.
  exists (@Rid bool), (fun b b' => b = negb b').
  rel.
    exists (negb a). destruct a; trivial.
    destruct b, b'; cbn in H0; congruence.
    destruct (left_total0 true). destruct x, H; cbn in H0; congruence.
Qed.
(* end hide *)

Lemma not_Surjective_Ror :
  exists (A B : Type) (R S : hrel A B),
    Surjective R /\ Surjective S /\ ~ Surjective (Ror R S).
(* begin hide *)
Proof.
  exists bool, bool.
  exists (@Rid bool), (fun b b' => b = negb b').
  rel.
    exists (negb a). destruct a; trivial.
    destruct b, b'; cbn in H0; congruence.
    cut (false = true).
      inversion 1.
      apply right_unique0 with false; auto.
Qed.
(* end hide *)

Lemma not_Surjective_Rnot :
  exists (A B : Type) (R : hrel A B),
    Surjective R /\ ~ Surjective (Rnot R).
(* begin hide *)
Proof.
  pose (A := option bool).
  exists A, A, (@eq A). rel.
  cut (Some true = Some false).
    inversion 1.
    apply right_unique0 with None; inversion 1.
Qed.
(* end hide *)

(** Właściwości relacji surjektywnych także są podobne do tych, jakie są
    udziałem relacji funkcyjnych. *)

(** ** Relacje bijektywne *)

Class Bijective {A B : Type} (R : hrel A B) : Prop :=
{
    B_Fun :> Functional R;
    B_LU :> LeftUnique R;
    B_RT :> RightTotal R;
}.

#[export]
Instance bij_to_Bijective :
  forall (A B : Type) (f : A -> B),
    bijective f -> Bijective (fun (a : A) (b : B) => f a = b).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Relacje funkcyjne, które są lewostronnie totalne (czyli injektywne) oraz
    prawostronnie totalne (czyli surjektywne), odpowiadają bijekcjom. *)

#[export]
Instance Bijective_eq :
  forall A : Type, Bijective (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Bijective_Rcomp :
  forall (A B C : Type) (R : hrel A B) (S : hrel B C),
    Bijective R -> Bijective S -> Bijective (Rcomp R S).
(* begin hide *)
Proof.
  split; destruct H, H0.
    apply Functional_Rcomp; assumption.
    apply LeftUnique_Rcomp; assumption.
    apply RightTotal_Rcomp; assumption.
Qed.
(* end hide *)

#[export]
Instance Bijective_Rinv :
  forall (A B : Type) (R : hrel A B),
    Bijective R -> Bijective (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Bijective_Rand :
  exists (A B : Type) (R S : hrel A B),
    Bijective R /\ Bijective S /\ ~ Bijective (Rand R S).
(* begin hide *)
Proof.
  exists bool, bool.
  exists (@Rid bool), (fun b b' => b = negb b').
  rel.
    exists (negb a). destruct a; trivial.
    destruct b, b'; cbn in H0; congruence.
    destruct (left_total0 true). destruct x, H; cbn in H0; congruence.
Qed.
(* end hide *)

Lemma not_Bijective_Ror :
  exists (A B : Type) (R S : hrel A B),
    Bijective R /\ Bijective S /\ ~ Bijective (Ror R S).
(* begin hide *)
Proof.
  exists bool, bool.
  exists (@Rid bool), (fun b b' => b = negb b').
  rel.
    exists (negb a). destruct a; trivial.
    destruct b, b'; cbn in H0; congruence.
    cut (false = true).
      inversion 1.
      apply right_unique0 with false; auto.
Qed.
(* end hide *)

Lemma not_Bijective_Rnot :
  exists (A B : Type) (R : hrel A B),
    Bijective R /\ ~ Bijective (Rnot R).
(* begin hide *)
Proof.
  pose (A := option bool).
  exists A, A, (@eq A). rel.
  cut (Some true = Some false).
    inversion 1.
    apply right_unique0 with None; inversion 1.
Qed.
(* end hide *)

(** Właściwości relacji bijektywnych różnią się jednym szalenie istotnym
    detalem od właściwości relacji funkcyjnych, injektywnych i surjektywnych:
    odwrotność relacji bijektywnej jest relacją bijektywną. *)

(** * Rodzaje relacji homogenicznych (TODO) *)

Definition rel (A : Type) : Type := hrel A A.

(** Relacje homogeniczne to takie, których wszystkie argumenty są tego
    samego typu. Warunek ten pozwala nam na wyrażenie całej gamy nowych
    właściwości, które relacje takie mogą posiadać.

    Uwaga terminologiczna: w innych pracach to, co nazwałem [Antireflexive]
    bywa zazwyczaj nazywane [Irreflexive]. Ja przyjąłem następujące reguły
    tworzenia nazw różnych rodzajów relacji:
    - "podstawowa" własność nie ma przedrostka, np. "zwrotna", "reflexive"
    - zanegowana własność ma przedrostek "nie" (lub podobny w nazwach
      angielskich), np. "niezwrotna", "irreflexive"
    - przeciwieństwo tej właściwości ma przedrostek "anty-" (po angielsku
      "anti-"), np. "antyzwrotna", "antireflexive" *)

(** ** Relacje zwrotne *)

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

(** Relacja [R] jest zwrotna (ang. reflexive), jeżeli każdy [x : A] jest
    w relacji sam ze sobą. Przykładem ze świata rzeczywistego może być
    relacja "x jest blisko y". Jest oczywiste, że każdy jest blisko samego
    siebie. *)

#[export]
Instance Reflexive_Empty :
  forall R : rel Empty_set, Reflexive R.
(* begin hide *)
Proof.
  split. destruct x.
Qed.
(* end hide *)

(** Okazuje się, że wszystkie relacje na typie pustym ([Empty_set]) są zwrotne.
    Nie powinno cię to w żaden sposób zaskakiwać — jest to tzw. pusta prawda
    (ang. vacuous truth), zgodnie z którą wszystkie zdania kwantyfikowane
    uniwersalnie po typie pustym są prawdziwe. Wszyscy w pustym pokoju są
    debilami. *)

#[export]
Instance Reflexive_eq {A : Type} : Reflexive (@eq A).
(* begin hide *)
Proof.
  split. intro. apply eq_refl.
Qed.
(* end hide *)

#[export]
Instance Reflexive_RTrue :
  forall A : Type, Reflexive (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Reflexive_RFalse_inhabited :
  forall A : Type, A -> ~ Reflexive (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Najważniejszym przykładem relacji zwrotnej jest równość. [eq] jest
    relacją zwrotną, gdyż ma konstruktor [eq_refl], który głosi, że
    każdy obiekt jest równy samemu sobie. Zwrotna jest też relacja
    [RTrue], gdyż każdy obiekt jest w jej przypadku w relacji z każdym,
    a więc także z samym sobą. Zwrotna nie jest za to relacja [RFalse]
    na typie niepustym, gdyż tam żaden obiekt nie jest w relacji z
    żadnym, a więc nie może także być w relacji z samym sobą. *)

Lemma eq_subrelation_Reflexive :
  forall (A : Type) (R : rel A),
    Reflexive R -> subrelation (@eq A) R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Równość jest "najmniejszą" relacją zwrotną w tym sensie, że jest ona
    subrelacją każdej relacji zwrotnej. Intuicyjnym uzasadnieniem jest
    fakt, że w definicji [eq] poza konstruktorem [eq_refl], który daje
    zwrotność, nie ma niczego innego. *)

Lemma Reflexive_subrelation_eq :
  forall (A : Type) (R : rel A),
    subrelation (@eq A) R -> Reflexive R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** TODO: Zachodzi też twierdzenie odwrotne. *)

#[export]
Instance Reflexive_Rcomp :
  forall (A : Type) (R S : rel A),
    Reflexive R -> Reflexive S -> Reflexive (Rcomp R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Reflexive_Rinv :
  forall (A : Type) (R : rel A),
    Reflexive R -> Reflexive (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Reflexive_Rand :
  forall (A : Type) (R S : rel A),
    Reflexive R -> Reflexive S -> Reflexive (Rand R S).
(* begin hide *)
Proof.
  destruct 1, 1. do 2 split; auto.
Qed.
(* end hide *)

#[export]
Instance Reflexive_Ror_l :
  forall (A : Type) (R S : rel A),
    Reflexive R -> Reflexive (Ror R S).
(* begin hide *)
Proof.
  destruct 1. unfold Ror; split. auto.
Qed.
(* end hide *)

#[export]
Instance Reflexive_Ror_r :
  forall (A : Type) (R S : rel A),
    Reflexive S -> Reflexive (Ror R S).
(* begin hide *)
Proof.
  intros A R S [HR].
  split; compute.
  intros x. right. apply HR.
Qed.
(* end hide *)

(** Jak widać, złożenie, odwrotność i koniunkcja relacji zwrotnych są zwrotne.
    Dysjunkcja posiada natomiast dużo mocniejszą właściwość: dysjunkcja
    dowolnej relacji z relacją zwrotną daje relację zwrotną. Tak więc
    dysjunkcja [R] z [eq] pozwala nam łatwo "dodać" zwrotność do [R]. Słownie
    dysjunkcja z [eq] odpowiada zwrotowi "lub równy", który możemy spotkać np.
    w wyrażeniach "mniejszy lub równy", "większy lub równy".

    Właściwością odwrotną do zwrotności jest antyzwrotność. Relacja
    antyzwrotna to taka, że żaden [x : A] nie jest w relacji sam ze sobą. *)

#[export]
Instance Antireflexive_neq :
  forall (A : Type), Antireflexive (fun x y : A => x <> y).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Antireflexive_lt : Antireflexive lt.
(* begin hide *)
Proof.
  split.
  (* TODO *) apply PeanoNat.Nat.nle_succ_diag_l.
Qed.
(* end hide *)

(** Typowymi przykładami relacji antyzwrotnych są nierówność [<>] oraz
    porządek "mniejszy niż" ([<]) na liczbach naturalnych. Ze względu
    na sposób działania ludzkiego mózgu antyzwrotna jest cała masa relacji
    znanych nam z codziennego życia: "x jest matką y", "x jest ojcem y",
    "x jest synem y", "x jest córką y", "x jest nad y", "x jest pod y",
    "x jest za y", "x jest przed y", etc. *)

Lemma Antireflexive_Empty :
  forall R : rel Empty_set, Antireflexive R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Antireflexive_eq_inhabited :
  forall A : Type, A -> ~ Antireflexive (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Antireflexive_RTrue_inhabited :
  forall A : Type, A -> ~ Antireflexive (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Antireflexive_RFalse :
  forall A : Type, Antireflexive (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Równość na typie niepustym nie jest antyzwrotna, gdyż jest zwrotna
    (wzajemne związki między tymi dwoma pojęciami zbadamy już niedługo).
    Antyzwrotna nie jest także relacja [RTrue] na typie niepustym, gdyż
    co najmniej jeden element jest w relacji z samym sobą. Antyzwrotna
    jest za to relacja pusta ([RFalse]). *)

Lemma not_Antireflexive_Rcomp :
  exists (A : Type) (R S : rel A),
    Antireflexive R /\ Antireflexive S /\
    ~ Antireflexive (Rcomp R S).
(* begin hide *)
Proof.
  pose (R := fun b b' => b = negb b').
  exists bool, R, R.
  cut (Antireflexive R).
  - rel. apply antireflexive0 with true. exists false. auto.
  - rel. destruct x; inversion 1.
Qed.
(* end hide *)

#[export]
Instance Antireflexive_Rinv :
  forall (A : Type) (R : rel A),
    Antireflexive R -> Antireflexive (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Antireflexive_Rand :
  forall (A : Type) (R S : rel A),
    Antireflexive R -> Antireflexive (Rand R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Antireflexive_Ror :
  forall (A : Type) (R S : rel A),
    Antireflexive R -> Antireflexive S -> Antireflexive (Ror R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Złożenie relacji antyzwrotnych nie musi być antyzwrotne, ale odwrotność
    i dysjunkcja już tak, zaś koniunkcja dowolnej relacji z relacją
    antyzwrotną daje nam relację antyzwrotną. Dzięki temu możemy dowolnej
    relacji [R] "zabrać" zwrotność koniunkcjując ją z [<>].

    Kolejną właściwością jest niezwrotność. Relacja niezwrotna to taka,
    która nie jest zwrotna. Zauważ, że pojęcie to zasadniczo różni się
    od pojęcia relacji antyzwrotnej: tutaj mamy kwantyfikator [exists],
    tam zaś [forall]. *)

#[export]
Instance Irreflexive_neq_inhabited :
  forall A : Type, A -> Irreflexive (Rnot (@eq A)).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Irreflexive_gt : Irreflexive gt.
(* begin hide *)
Proof.
  rel. exists 0. inversion 1.
Qed.
(* end hide *)

(** Typowym przykładem relacji niezwrotnej jest nierówność [x <> y]. Jako,
    że każdy obiekt jest równy samemu sobie, to żaden obiekt nie może być
    nierówny samemu sobie. Zauważ jednak, że typ [A] musi być niepusty,
    gdyż w przeciwnym wypadku nie mamy czego dać kwantyfikatorowi
    [exists].

    Innym przykładem relacji niezwrotnej jest porządek "większy niż"
    na liczbach naturalnych. Porządkami zajmiemy się już niedługo. *)

Lemma not_Irreflexive_Empty :
  forall R : rel Empty_set, ~ Irreflexive R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Irreflexive_eq_Empty :
  ~ Irreflexive (@eq Empty_set).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Irreflexive_eq_inhabited :
  forall A : Type, A -> ~ Irreflexive (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Równość jest zwrotna, a więc nie może być niezwrotna. Zauważ jednak,
    że musimy podać aż dwa osobne dowody tego faktu: jeden dla typu
    pustego [Empty_set], a drugi dla dowolnego typu niepustego. Wynika to
    z tego, że nie możemy sprawdzić, czy dowolny typ [A] jest pusty, czy
    też nie. *)

Lemma not_Irreflexive_RTrue_Empty :
  ~ Irreflexive (@RTrue Empty_set Empty_set).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Irreflexive_RTrue_inhabited :
  forall A : Type, A -> ~ Irreflexive (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Irreflexive_RFalse_Empty :
  ~ Irreflexive (@RFalse Empty_set Empty_set).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Irreflexive_RFalse_inhabited :
  forall A : Type, A -> Irreflexive (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Podobnej techniki możemy użyć, aby pokazać, że relacja pełna ([RTrue])
    nie jest niezwrotna. Inaczej jest jednak w przypadku [RFalse] — na typie
    pustym nie jest ona niezwrotna, ale na dowolnym typie niepustym już
    owszem. *)

Lemma not_Irreflexive_Rcomp :
  exists (A : Type) (R S : rel A),
    Irreflexive R /\ Irreflexive S /\ ~ Irreflexive (Rcomp R S).
(* begin hide *)
Proof.
  exists bool. pose (R := fun b b' => b = negb b').
  exists R, R. cut (Irreflexive R).
    rel. eapply (H0 (negb x0)). destruct x0; auto.
    split. exists true. unfold R. inversion 1.
Qed.
(* end hide *)

(** Złożenie relacji niezwrotnych nie musi być niezwrotne. Przyjrzyj się
    uważnie definicji [Rcomp], a z pewnością uda ci się znaleźć jakiś
    kontrprzykład. *)

#[export]
Instance Irreflexive_Rinv :
  forall (A : Type) (R : rel A),
    Irreflexive R -> Irreflexive (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Irreflexive_Rand_l :
  forall (A : Type) (R S : rel A),
    Irreflexive R -> Irreflexive (Rand R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Irreflexive_Rand_r :
  forall (A : Type) (R S : rel A),
    Irreflexive S -> Irreflexive (Rand R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Irreflexive_Ror :
  exists (A : Type) (R S : rel A),
    Irreflexive R /\ Irreflexive S /\ ~ Irreflexive (Ror R S).
(* begin hide *)
Proof.
  exists
    bool,
    (fun x y : bool => if x then x = negb y else x = y),
    (fun x y : bool => if x then x = y else x = negb y).
  rel.
  - exists true; cbn. inversion 1.
  - exists false; cbn. inversion 1.
  - destruct x; auto.
Qed.
(* end hide *)

(** Odwrotność relacji niezwrotnej jest niezwrotna. Koniunkcja dowolnej
    relacji z relacją niezwrotną daje relację niezwrotną. Tak więc za
    pomocą koniunkcji i dysjunkcji możemy łatwo dawać i zabierać
    zwrotność różnym relacjom. Okazuje się też, że dysjunkcja nie
    zachowuje niezwrotności.

    Na zakończenie zbadajmy jeszcze, jakie związki zachodzą pomiędzy
    zwrotnością, antyzwrotnością i niezwrotnością. *)

#[export]
Instance Reflexive_Rnot :
  forall (A : Type) (R : rel A),
    Antireflexive R -> Reflexive (Rnot R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Antireflexive_Rnot :
  forall (A : Type) (R : rel A),
    Reflexive R -> Antireflexive (Rnot R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Podstawowa zależność między nimi jest taka, że negacja relacji zwrotnej
    jest antyzwrotna, zaś negacja relacji antyzwrotnej jest zwrotna. *)

Lemma Reflexive_Antireflexive_Empty :
  forall R : rel Empty_set, Reflexive R /\ Antireflexive R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma Reflexive_Antireflexive_inhabited :
  forall (A : Type) (R : rel A),
    A -> Reflexive R -> Antireflexive R -> False.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Każda relacja na typie pustym jest jednocześnie zwrotna i antyzwrotna,
    ale nie może taka być żadna relacja na typie niepustym. *)

#[export]
Instance Irreflexive_inhabited_Antireflexive :
  forall (A : Type) (R : rel A),
    A -> Antireflexive R -> Irreflexive R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Związek między niezwrotnością i antyzwrotnością jest nadzwyczaj prosty:
    każda relacja antyzwrotna na typie niepustym jest też niezwrotna. *)

(** ** Relacje symetryczne *)

Class Symmetric {A : Type} (R : rel A) : Prop :=
{
    symmetric : forall x y : A, R x y -> R y x
}.

Class Antisymmetric {A : Type} (R : rel A) : Prop :=
{
    antisymmetric : forall x y : A, R x y -> ~ R y x
}.

Class Asymmetric {A : Type} (R : rel A) : Prop :=
{
    asymmetric : exists x y : A, R x y /\ ~ R y x
}.

(** Relacja jest symetryczna, jeżeli kolejność podawania argumentów nie
    ma znaczenia. Przykładami ze świata rzeczywistego mogą być np. relacje
    "jest blisko", "jest obok", "jest naprzeciwko". *)

Lemma Symmetric_char :
  forall (A : Type) (R : rel A),
    Symmetric R <-> (Rinv R <--> R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Alterntywną charakteryzacją symetrii może być stwierdzenie, że relacja
    symetryczna to taka, która jest swoją własną odwrotnością. *)

#[export]
Instance Symmetric_Empty :
  forall R : rel Empty_set, Symmetric R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Symmetric_eq :
  forall A : Type, Symmetric (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Symmetric_RTrue :
  forall A : Type, Symmetric (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Symmetric_RFalse :
  forall A : Type, Symmetric (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Równość, relacja pełna i pusta są symetryczne. *)

Lemma not_Symmetric_Rcomp :
  exists (A : Type) (R S : rel A),
    Symmetric R /\ Symmetric S /\ ~ Symmetric (Rcomp R S).
(* begin hide *)
Proof.
  pose (R := fun b b' : bool => if b then b = negb b' else True).
  pose (S := fun b b' : bool => if negb b' then b = negb b' else True).
  exists bool, R, S. repeat split.
    unfold R. destruct x, y; auto.
    unfold S. destruct x, y; cbn; auto.
    unfold Rcomp. destruct 1. edestruct (symmetric0 false true).
      exists true. unfold R, S. cbn. auto.
      unfold R, S in H. destruct x, H; cbn in *; congruence.
Qed.
(* end hide *)

(** Złożenie relacji symetrycznych nie musi być symetryczne. *)

#[export]
Instance Symmetric_Rinv :
  forall (A : Type) (R : rel A),
    Symmetric R -> Symmetric (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Symmetric_Rand :
  forall (A : Type) (R S : rel A ),
    Symmetric R -> Symmetric S -> Symmetric (Rand R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Symmetric_Ror :
  forall (A : Type) (R S : rel A ),
    Symmetric R -> Symmetric S -> Symmetric (Ror R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Symmetric_Rnot :
  forall (A : Type) (R : rel A),
    Symmetric R -> Symmetric (Rnot R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Pozostałe operacje (odwracanie, koniunkcja, dysjunkcja, negacja)
    zachowują symetrię.

    Relacja antysymetryczna to przeciwieństwo relacji symetrycznej —
    jeżeli [x] jest w relacji z [y], to [y] nie może być w relacji z
    [x]. Sporą klasę przykładów stanowią różne relacje służące do
    porównywania: "x jest wyższy od y", "x jest silniejszy od y",
    "x jest bogatszy od y". *)

Lemma Antisymmetric_Empty :
  forall R : rel Empty_set, Antisymmetric R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Antisymmetric_eq_inhabited :
  forall A : Type, A -> ~ Antisymmetric (@eq A).
(* begin hide *)
Proof.
  intros A x. destruct 1. apply (antisymmetric0 x x); trivial.
Qed.
(* end hide *)

Lemma not_Antisymmetric_RTrue_inhabited :
  forall A : Type, A -> ~ Antisymmetric (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance RFalse_Antiymmetric :
  forall A : Type, Antisymmetric (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Każda relacja na typie pustym jest antysymetryczna. Równość nie jest
    antysymetryczna, podobnie jak relacja pełna (ale tylko na typie
    niepustym). Relacja pusta jest antysymetryczna, gdyż przesłanka [R x y]
    występująca w definicji antysymetrii jest zawsze fałszywa. *)

(* begin hide *)
Require Import Arith.

Fixpoint lookup (p : nat * nat) (l : list (nat * nat)) : bool :=
match l with
| [] => false
| (h1, h2) :: t =>
  if andb (beq_nat (fst p) h1) (beq_nat (snd p) h2)
  then true
  else lookup p t
end.
(* end hide *)

Lemma not_Antisymmetric_Rcomp :
  exists (A : Type) (R S : rel A),
    Antisymmetric R /\ Antisymmetric S /\
    ~ Antisymmetric (Rcomp R S).
(* begin hide *)
Proof.
  pose (R := fun n m : nat =>
    lookup (n, m) [(1, 2); (1, 3); (1, 4); (2, 4)] = true).
  pose (S := fun n m : nat =>
    lookup (n, m) [(4, 1); (4, 2); (4, 3)] = true).
  exists nat, R, S. repeat split.
    destruct x as [| [| [| [| [| x]]]]],
             y as [| [| [| [| [| y]]]]];
      compute; inversion 1; inversion 1.
    destruct x as [| [| [| [| [| x]]]]],
             y as [| [| [| [| [| y]]]]];
      compute; inversion 1; inversion 1.
    unfold Rcomp. destruct 1. apply (antisymmetric0 1 2).
      exists 4. compute. auto.
      exists 4. compute. auto.
Qed.
(* end hide *)

#[export]
Instance Antisymmetric_Rinv :
  forall (A : Type) (R : rel A),
    Antisymmetric R -> Antisymmetric (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Antisymmetric_Rand :
  forall (A : Type) (R S : rel A),
    Antisymmetric R -> Antisymmetric (Rand R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Antisymmetric_Ror :
  exists (A : Type) (R S : rel A),
    Antisymmetric R /\ Antisymmetric S /\
    ~ Antisymmetric (Ror R S).
(* begin hide *)
Proof.
  pose (R := fun n m : nat =>
    lookup (n, m) [(1, 2); (1, 3); (1, 4); (2, 4)] = true).
  pose (S := fun n m : nat =>
    lookup (n, m) [(4, 1); (4, 2); (4, 3)] = true).
  exists nat, R, S. repeat split.
    destruct x as [| [| [| [| [| x]]]]],
             y as [| [| [| [| [| y]]]]];
      compute; inversion 1; inversion 1.
    destruct x as [| [| [| [| [| x]]]]],
             y as [| [| [| [| [| y]]]]];
      compute; inversion 1; inversion 1.
    unfold Ror. destruct 1. apply (antisymmetric0 1 4).
      compute. auto.
      compute. auto.
Qed.
(* end hide *)

Lemma not_Antisymmetric_Rnot :
  exists (A : Type) (R : rel A),
    Antisymmetric R /\ ~ Antisymmetric (Rnot R).
(* begin hide *)
Proof.
  pose (R := fun b b' : bool => if b then b = negb b' else False).
  exists bool, R. repeat split; intros.
    destruct x, y; compute in *; intuition.
    rel. apply (antisymmetric0 true true); inversion 1.
Qed.
(* end hide *)

Lemma not_Asymmetric_Empty :
  forall R : rel Empty_set, ~ Asymmetric R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Asymmetric_Rcomp :
  exists (A : Type) (R S : rel A),
    Asymmetric R /\ Asymmetric S /\ ~ Asymmetric (Rcomp R S).
(* begin hide *)
Proof.
  pose (R := fun b b' : bool => if b then b = negb b' else False).
  pose (S := fun b b' : bool => if negb b' then b = negb b' else False).
  exists bool, R, S. repeat split.
    exists true, false. cbn. auto.
    exists true, false. cbn. auto.
    unfold Rcomp; destruct 1.
      destruct asymmetric0 as [b1 [b2 [[b3 H] H']]].
      destruct b1, b2, b3; cbn in H; destruct H; inversion H; inversion H0.
Qed.
(* end hide *)

#[export]
Instance Asymmetric_Rinv :
  forall (A : Type) (R : rel A),
    Asymmetric R -> Asymmetric (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Asymmetric_Rand :
  exists (A : Type) (R S : rel A),
    Asymmetric R /\ Asymmetric S /\ ~ Asymmetric (Rand R S).
(* begin hide *)
Proof.
  pose (R := fun n m : nat =>
    lookup (n, m) [(1, 0)] = true).
  pose (S := fun n m : nat =>
    lookup (n, m) [(0, 1)] = true).
  exists nat, R, S. repeat split.
    exists 1, 0. compute. rel.
    exists 0, 1. compute. rel.
    unfold Rand. destruct 1. decompose [ex and] asymmetric0.
      destruct x as [| [| x]],
               x0 as [| [| x0]];
      compute in *; eauto.
Qed.
(* end hide *)

Lemma not_Asymmetric_Ror :
  exists (A : Type) (R S : rel A),
    Asymmetric R /\ Asymmetric S /\ ~ Asymmetric (Ror R S).
(* begin hide *)
Proof.
  pose (R := fun b b' : bool => if b then True else False).
  pose (S := fun b b' : bool => if b' then True else False).
  exists bool, R, S. repeat split; intros.
    exists true, false. cbn. auto.
    exists false, true. cbn. auto.
    destruct 1. destruct asymmetric0 as [x [y [H H']]].
      destruct x, y; firstorder.
Qed.
(* end hide *)

(** ** Relacje przechodnie *)

Class Transitive {A : Type} (R : rel A) : Prop :=
{
    transitive : forall x y z : A, R x y -> R y z -> R x z
}.

#[export]
Instance Transitive_RTrue :
  forall A : Type, Transitive (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Transitive_RFalse :
  forall A : Type, Transitive (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Transitive_eq :
  forall A : Type, Transitive (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Transitive_Rinv :
  forall (A : Type) (R : rel A),
    Transitive R -> Transitive (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Transitive_Rcomp :
  exists (A : Type) (R S : rel A),
    Transitive R /\ Transitive S /\ ~ Transitive (Rcomp R S).
(* begin hide *)
Proof.
  pose (R := fun n m : nat =>
    lookup (n, m) [(0, 1); (2, 3)] = true).
  pose (S := fun n m : nat =>
    lookup (n, m) [(1, 2); (3, 4)] = true).
  exists nat, R, S. repeat split.
    destruct x as [| [| [|]]], y as [| [| [|]]], z as [| [| [|]]]; compute;
      try congruence.
    destruct x as [| [| [| [|]]]], y as [| [| [| [|]]]], z as [| [| [| [|]]]];
      compute; try congruence.
    unfold Rcomp; destruct 1.
      destruct (transitive0 0 2 4).
        exists 1. compute. auto.
        exists 3. compute. auto.
        destruct x as [| [|]]; compute in H; rel; congruence.
Qed.
(* end hide *)

Lemma not_Transitive_Rnot :
  exists (A : Type) (R : rel A),
    Transitive R /\ ~ Transitive (Rnot R).
(* begin hide *)
Proof.
  exists bool, (@eq bool); split.
  - split. intros x y z -> ->. reflexivity.
  - intros [HT]; unfold Rnot in *.
    destruct (HT true false true); congruence.
Qed.
(* end hide *)

Lemma not_Transitive_Ror :
  exists (A : Type) (R S : rel A),
    Transitive R /\ Transitive S /\ ~ Transitive (Ror R S).
(* begin hide *)
Proof.
  exists bool, (fun x _ => x = true), (fun _ y => y = true).
  split; [| split]; [rel | rel |].
  intros [HT]; unfold Ror in HT.
  destruct (HT false true false); intuition congruence.
Qed.
(* end hide *)

#[export]
Instance Transitive_Rand :
  forall (A : Type) (R S : rel A),
    Transitive R -> Transitive S -> Transitive (Rand R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** ** Relacje równoważności *)

Class Equivalence {A : Type} (R : rel A) : Prop :=
{
    Equivalence_Reflexive :> Reflexive R;
    Equivalence_Symmetric :> Symmetric R;
    Equivalence_Transitive :> Transitive R;
}.

#[export]
Instance Equivalence_RTrue :
  forall A : Type, Equivalence (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Equivalence_Empty :
  forall R : rel Empty_set, Equivalence R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Equivalence_RFalse_inhabited :
  forall A : Type,
    A -> ~ Equivalence (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Equivalence_eq :
  forall A : Type,
    Equivalence (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Equivalence_Rinv :
  forall (A : Type) (R : rel A),
    Equivalence R -> Equivalence (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Equivalence_Rcomp :
  exists (A : Type) (R S : rel A),
    Equivalence R /\ Equivalence S /\ ~ Equivalence (Rcomp R S).
(* begin hide *)
Proof.
  Axiom f g : nat -> nat.
  Axiom f_0 : f 0 = 0.
  Axiom g_1 : g 1 = 1.
  Axiom f_2 : f 2 = 0.
  Axiom g_2 : g 2 = 1.
  exists
    nat,
    (fun x y => f x = f y),
    (fun x y => g x = g y).
  split; [| split].
  - rel.
  - rel.
  - unfold Rcomp; intros [[HR] [HS] [HT]].
    specialize (HS 0 1).
    assert (exists b : nat, f 0 = f b /\ g b = g 1).
    {
      exists 2. split.
      - rewrite f_0, f_2. reflexivity.
      - rewrite g_1, g_2. reflexivity.
    }
    specialize (HS H).
    destruct HS as (b & H1 & H2).
Abort.
(* end hide *)

Lemma not_Equivalence_Rnot :
  exists (A : Type) (R : rel A),
    Equivalence R /\ ~ Equivalence (Rnot R).
(* begin hide *)
Proof.
  exists bool, (@eq bool).
  split.
  - apply Equivalence_eq.
  - intros [R _ _]. apply (Reflexive_Antireflexive_inhabited bool (Rnot eq)).
    + exact true.
    + assumption.
    + apply Antireflexive_Rnot. typeclasses eauto.
Qed.
(* end hide *)

(* begin hide *)
Inductive Threee : Type := One | Two | Three.

Definition wut (x y : Threee) : Prop :=
match x, y with
| One  , One   => True
| Two  , Two   => True
| Three, Three => True
| One  , Two   => True
| Two  , One   => True
| _    , _     => False
end.

Definition wut' (x y : Threee) : Prop :=
match x, y with
| One  , One   => True
| Two  , Two   => True
| Three, Three => True
| One  , Three => True
| Three, One   => True
| _    , _     => False
end.
(* end hide *)

Lemma not_Equivalence_Ror :
  exists (A : Type) (R S : rel A),
    Equivalence R /\ Equivalence S /\ ~ Equivalence (Ror R S).
(* begin hide *)
Proof.
  exists
    (list nat),
    (fun l1 l2 => length l1 = length l2),
    (fun l1 l2 => head l1 = head l2).
  repeat split; intros.
  - rewrite H. reflexivity.
  - rewrite H, H0. reflexivity.
  - rewrite H. reflexivity.
  - rewrite H, H0. reflexivity.
  - destruct 1 as [R S [T]].
    specialize (T [1] [2] [2; 3]).
    compute in T. intuition congruence.
Qed.
(* end hide *)

#[export]
Instance Equivalence_Rand :
  forall (A : Type) (R S : rel A),
    Equivalence R -> Equivalence S -> Equivalence (Rand R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** ** Częściowe relacje równoważności *)

Class PER {A : Type} (R : rel A) : Prop :=
{
    PER_Symmetric :> Symmetric R;
    PER_Transitive :> Transitive R;
}.

#[export]
Instance PER_Empty :
  forall R : rel Empty_set, PER R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance PER_RTrue :
  forall A : Type, PER (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance PER_RFalse :
  forall A : Type, PER (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance PER_eq :
  forall A : Type, PER (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance PER_Rinv :
  forall (A : Type) (R : rel A),
    PER R -> PER (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_PER_Rcomp :
  exists (A : Type) (R S : rel A),
    PER R /\ PER S /\ ~ PER (Rcomp R S).
(* begin hide *)
Proof.
  exists
    nat,
    (fun x y => f x = f y),
    (fun x y => g x = g y).
  split; [| split].
  - rel.
  - rel.
  - unfold Rcomp; intros [[HS] [HT]].
    specialize (HS 0 1).
    assert (exists b : nat, f 0 = f b /\ g b = g 1).
    {
      exists 2. split.
      - rewrite f_0, f_2. reflexivity.
      - rewrite g_1, g_2. reflexivity.
    }
    specialize (HS H).
    destruct HS as (b & H1 & H2).
Abort.
(* end hide *)

Lemma not_PER_Rnot :
  exists (A : Type) (R : rel A),
    PER R /\ ~ PER (Rnot R).
(* begin hide *)
Proof.
  exists bool, (@eq bool).
  split.
  - apply PER_eq.
  - unfold Rnot; intros [[HS] [HT]].
    specialize (HT true false true).
    destruct HT; congruence.
Qed.
(* end hide *)

Lemma not_PER_Ror :
  exists (A : Type) (R S : rel A),
    PER R /\ PER S /\ ~ PER (Ror R S).
(* begin hide *)
Proof.
  exists
    (list nat),
    (fun l1 l2 => length l1 = length l2),
    (fun l1 l2 => head l1 = head l2).
  split; [| split].
  - rel.
  - rel.
  - intros [S [T]].
    specialize (T [1] [2] [2; 3]).
    compute in T. intuition congruence.
Qed.
(* end hide *)

#[export]
Instance PER_Rand :
  forall (A : Type) (R S : rel A),
    PER R -> PER S -> PER (Rand R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** ** Relacje tolerancji *)

Class Tolerance {A : Type} (R : rel A) : Prop :=
{
    Tolerance_Reflexive :> Reflexive R;
    Tolerance_Symmetric :> Symmetric R;
}.

#[export]
Instance Tolerance_Empty :
  forall R : rel Empty_set, Tolerance R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Tolerance_RTrue :
  forall A : Type, Tolerance (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Tolerance_RFalse_inhabited :
  forall A : Type, A -> ~ Tolerance (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Tolerance_eq :
  forall A : Type, Tolerance (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Tolerance_Rinv :
  forall (A : Type) (R : rel A),
    Tolerance R -> Tolerance (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Tolerance_Rcomp :
  exists (A : Type) (R S : rel A),
    Tolerance R /\ Tolerance S /\ ~ Tolerance (Rcomp R S).
(* begin hide *)
Proof.
  exists
    nat,
    (fun x y =>
      x = y
        \/
      x = 0 /\ y = 1
        \/
      x = 1 /\ y = 0),
    (fun x y =>
      x = y
        \/
      x = 2 /\ y = 3
        \/
      x = 3 /\ y = 2).
  split; [| split].
  - rel.
  - rel.
  - unfold Rcomp. intros [[HR] [HS]].
    destruct (HS 2 3).
    + exists 2. lia.
    + decompose [and or] H; subst; try lia.
Abort.
(* end hide *)

Lemma not_Tolerance_Rnot :
  exists (A : Type) (R : rel A),
    Tolerance R /\ ~ Tolerance (Rnot R).
(* begin hide *)
Proof.
  exists bool, (@eq bool).
  split.
  - apply Tolerance_eq.
  - unfold Rnot; intros [[HS] [HT]].
    destruct (HS true). reflexivity.
Qed.
(* end hide *)

#[export]
Instance Tolerance_Ror :
  forall {A : Type} (R S : rel A),
    Tolerance R -> Tolerance S -> Tolerance (Ror R S).
(* begin hide *)
Proof.
  intros A R S [[RR] [RS]] [[SR] [SS]].
  split; split; unfold Ror.
  - intros x. left; apply RR; assumption.
  - intros x y [rxy | sxy].
    + left; apply RS; assumption.
    + right; apply SS; assumption.
Qed.
(* end hide *)

#[export]
Instance Tolerance_Rand :
  forall (A : Type) (R S : rel A),
    Tolerance R -> Tolerance S -> Tolerance (Rand R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** ** Relacje słaboantysymetryczne *)

Class WeaklyAntisymmetric {A : Type} (R : rel A) : Prop :=
{
    weakly_antisymmetric : forall x y : A, R x y -> R y x -> x = y
}.

#[export]
Instance WeaklyAntisymmetric_Empty :
  forall R : rel Empty_set, WeaklyAntisymmetric R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance WeaklyAntisymmetric_hProp :
  forall {A : Type} (R : rel A),
    (forall x y : A, x = y) ->
      WeaklyAntisymmetric R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_WeaklyAntisymmetric_RTrue_doubleton :
  forall {A : Type} {x y : A},
    x <> y -> ~ WeaklyAntisymmetric (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance WeaklyAntisymmetric_RFalse :
  forall A : Type, WeaklyAntisymmetric (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance WeaklyAntisymmetric_Rinv :
  forall (A : Type) (R : rel A),
    WeaklyAntisymmetric R -> WeaklyAntisymmetric (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_WeaklyAntisymmetric_Rcomp :
  exists (A : Type) (R S : rel A),
    WeaklyAntisymmetric R /\ WeaklyAntisymmetric S /\
      ~ WeaklyAntisymmetric (Rcomp R S).
(* begin hide *)
Proof.
  pose (R := fun b b' : bool =>
    if orb (andb b (negb b')) (andb (negb b) (negb b')) then True else False).
  pose (S := fun b b' : bool =>
    if orb (andb (negb b) b') (andb (negb b) (negb b')) then True else False).
  exists bool, R, S. repeat split.
    destruct x, y; cbn; do 2 inversion 1; auto.
    destruct x, y; cbn; do 2 inversion 1; auto.
    unfold Rcomp; destruct 1. cut (true = false).
      inversion 1.
      apply weakly_antisymmetric0.
        exists false. cbn. auto.
        exists false. cbn. auto.
Qed.
(* end hide *)

Lemma not_WeaklyAntisymmetric_Rnot :
  exists (A : Type) (R : rel A),
    WeaklyAntisymmetric R /\ ~ WeaklyAntisymmetric (Rnot R).
(* begin hide *)
Proof.
  pose (R := fun b b' : bool => if andb b b' then True else False).
  exists bool, R. repeat split; intros.
    destruct x, y; compute in *; intuition.
    unfold Rnot; destruct 1.
      cut (true = false).
        inversion 1.
        apply weakly_antisymmetric0; auto.
Qed.
(* end hide *)

Lemma not_WeaklyAntisymmetric_Ror :
  exists (A : Type) (R S : rel A),
    WeaklyAntisymmetric R /\ WeaklyAntisymmetric S /\
      ~ WeaklyAntisymmetric (Ror R S).
(* begin hide *)
Proof.
  pose (R := fun b b' : bool =>
    if orb (andb b (negb b')) (andb (negb b) (negb b')) then True else False).
  pose (S := fun b b' : bool =>
    if orb (andb (negb b) b') (andb (negb b) (negb b')) then True else False).
  exists bool, R, S. repeat split.
    destruct x, y; cbn; do 2 inversion 1; auto.
    destruct x, y; cbn; do 2 inversion 1; auto.
    unfold Ror; destruct 1. cut (true = false).
      inversion 1.
      apply weakly_antisymmetric0; cbn; auto.
Qed.
(* end hide *)

#[export]
Instance WeaklyAntisymmetric_Rand :
  forall (A : Type) (R S : rel A),
    WeaklyAntisymmetric R -> WeaklyAntisymmetric S ->
      WeaklyAntisymmetric (Rand R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** ** Relacje totalne *)

Class Total {A : Type} (R : rel A) : Prop :=
{
    total : forall x y : A, R x y \/ R y x
}.

#[export]
Instance Total_RTrue :
  forall A : Type,
    Total (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma Total_RFalse_Empty :
  Total (@RFalse Empty_set Empty_set).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Total_RFalse_inhabited :
  forall A : Type,
    A -> ~ Total (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma Total_eq_Empty :
  Total (@eq Empty_set).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma Total_eq_unit :
  Total (@eq unit).
(* begin hide *)
Proof. rel. auto. Qed.
(* end hide *)

Lemma not_Total_eq_two_elems :
  forall {A : Type} {x y : A},
    x <> y -> ~ Total (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Total_Rcomp :
  forall (A : Type) (R S : rel A),
    Total R -> Total S -> Total (Rcomp R S).
(* begin hide *)
Proof.
  intros A R S [HR] [HS].
  unfold Rcomp; split; intros x y.
  destruct (HR x y).
  - destruct (HS x y).
    + left. exists x. firstorder.
    + left. exists y. firstorder.
  - destruct (HS x y).
    + right. exists x. firstorder.
    + right. exists y. firstorder.
Qed.
(* end hide *)

#[export]
Instance Total_Rinv :
  forall (A : Type) (R : rel A),
    Total R -> Total (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Total_Rnot :
  exists (A : Type) (R : rel A),
    Total R /\ ~ Total (Rnot R).
(* begin hide *)
Proof.
  pose (R := fun b b' : bool => b = negb b' \/ b = b).
  exists bool, R. repeat split; intros.
    destruct x, y; compute; auto.
    unfold Rnot; destruct 1.
      destruct (total0 true false); compute in *; intuition.
Qed.
(* end hide *)

#[export]
Instance Total_Ror :
  forall (A : Type) (R S : rel A),
    Total R -> Total S -> Total (Ror R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Total_Rand :
  exists (A : Type) (R S : rel A),
    Total R /\ Total S /\ ~ Total (Rand R S).
(* begin hide *)
Proof.
  pose (R := fun b b' =>
  match b, b' with
  | true, _ => True
  | false, false => True
  | _, _ => False
  end).
  pose (S := fun b b' =>
  match b, b' with
  | false, _ => True
  | true, true => True
  | _, _ => False
  end).
  exists bool, R, S. repeat split; intros.
    destruct x, y; cbn; auto.
    destruct x, y; cbn; auto.
    unfold Rand; destruct 1.
      decompose [and or] (total0 false true); cbn in *; assumption.
Qed.
(* end hide *)

#[export]
Instance Reflexive_Total :
  forall (A : Type) (R : rel A),
    Total R -> Reflexive R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma Total_Symmetric_char :
  forall {A : Type} (R : rel A),
    Total R -> Symmetric R -> R <--> RTrue.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** ** Porządki *)

Class Preorder {A : Type} (R : rel A) : Prop :=
{
    Preorder_Reflexive :> Reflexive R;
    Preorder_Transitive :> Transitive R;
}.

Class PartialOrder {A : Type} (R : rel A) : Prop :=
{
    PartialOrder_Preorder :> Preorder R;
    PartialOrder_WeaklyAntisymmetric :> WeaklyAntisymmetric R;
}.

Class TotalOrder {A : Type} (R : rel A) : Prop :=
{
    TotalOrder_PartialOrder :> PartialOrder R;
    TotalOrder_Total :> Total R;
}.

Class TotalPreorder {A : Type} (R : rel A) : Prop :=
{
    TotalPreorder_PartialOrder :> Preorder R;
    TotalPreorder_Total :> Total R;
}.

(** ** Relacje słabo totalne *)

Class WeaklyTotal {A : Type} (R : rel A) : Prop :=
{
    weakly_total : forall x y : A, ~ R x y -> R y x
}.

#[export]
Instance WeaklyTotal_RTrue :
  forall A : Type,
    WeaklyTotal (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma WeaklyTotal_Empty :
  forall R : rel Empty_set, WeaklyTotal R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_WeaklyTotal_RFalse_inhabited :
  forall A : Type,
    A -> ~ WeaklyTotal (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma WeaklyTotal_eq_Empty :
  WeaklyTotal (@eq Empty_set).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma WeaklyTotal_eq_unit :
  WeaklyTotal (@eq unit).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_WeaklyTotal_eq_two_elems :
  forall {A : Type} {x y : A},
    x <> y -> ~ WeaklyTotal (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance WeaklyTotal_Rinv :
  forall (A : Type) (R : rel A),
    WeaklyTotal R -> WeaklyTotal (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance WeaklyTotal_Rcomp :
  forall (A : Type) (R S : rel A),
    WeaklyTotal R -> WeaklyTotal S -> WeaklyTotal (Rcomp R S).
(* begin hide *)
Proof.
  intros A R S [HR] [HS].
  unfold Rcomp; split; intros x y H.
Abort.
(* end hide *)

Lemma not_WeaklyTotal_Rnot :
  exists (A : Type) (R : rel A),
    WeaklyTotal R /\ ~ WeaklyTotal (Rnot R).
(* begin hide *)
Proof.
  exists unit, RTrue.
  split; rel.
Qed.
(* end hide *)

#[export]
Instance WeaklyTotal_Ror :
  forall (A : Type) (R S : rel A),
    WeaklyTotal R -> WeaklyTotal S -> WeaklyTotal (Ror R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_WeaklyTotal_Rand :
  exists (A : Type) (R S : rel A),
    WeaklyTotal R /\ WeaklyTotal S /\ ~ WeaklyTotal (Rand R S).
(* begin hide *)
Proof.
  exists bool, (fun x y => x = true \/ y = false), (fun x y => x = false \/ y = true).
  split; [| split].
  - rel. destruct y; rel.
  - rel. destruct y; rel.
  - intros [H]; unfold Rand in H.
    specialize (H true false).
    intuition.
Qed.
(* end hide *)

Lemma not_Antireflexive_WeaklyTotal_inhabited :
  forall (A : Type) (R : rel A) (x : A),
    WeaklyTotal R -> ~ Antireflexive R.
(* begin hide *)
Proof.
  intros A R x [HWT] [HA]. rel.
Qed.
(* end hide *)

(** ** Relacje trychotomiczne *)

Class Trichotomous {A : Type} (R : rel A) : Prop :=
{
    trichotomous : forall x y : A, R x y \/ x = y \/ R y x
}.

#[export]
Instance Trichotomous_Total :
  forall (A : Type) (R : rel A),
    Total R -> Trichotomous R.
(* begin hide *)
Proof.
  destruct 1. split. intros. destruct (total0 x y).
    left. assumption.
    do 2 right. assumption.
Qed.
(* end hide *)

#[export]
Instance Trichotomous_Empty :
  forall R : rel Empty_set, Trichotomous R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Trichotomous_RTrue :
  forall A : Type, Trichotomous (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Trichotomous_RFalse_subsingleton :
  forall A : Type, (forall x y : A, x = y) -> Trichotomous (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Trichotomous_RFalse_two_elems :
  forall {A : Type} {x y : A},
    x <> y -> ~ Trichotomous (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Trichotomous_eq_subsingleton :
  forall A : Type, (forall x y : A, x = y) -> Trichotomous (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Trichotomous_eq :
  exists A : Type, ~ Trichotomous (@eq A).
(* begin hide *)
Proof.
  exists bool. destruct 1. destruct (trichotomous0 true false); rel.
Qed.
(* end hide *)

#[export]
Instance Trichotomous_Rinv :
  forall (A : Type) (R : rel A),
    Trichotomous R -> Trichotomous (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Trichotomous_Rcomp :
  exists (A : Type) (R S : rel A),
    Trichotomous R /\ Trichotomous S /\ ~ Trichotomous (Rcomp R S).
(* begin hide *)
Proof.
  exists nat, lt, lt. split; [idtac | split].
  1-2: split; lia.
    destruct 1. unfold Rcomp in *. specialize (trichotomous0 0 1).
      decompose [and or ex] trichotomous0; clear trichotomous0.
        all: lia.
Qed.
(* end hide *)

Lemma not_Trichotomous_Rnot :
  exists (A : Type) (R : rel A),
    Trichotomous R /\ ~ Trichotomous (Rnot R).
(* begin hide *)
Proof.
  pose (R := fun b b' : bool => b = negb b').
  exists bool, R. repeat split; intros.
    destruct x, y; compute; auto.
    unfold Rnot; destruct 1.
      destruct (trichotomous0 true false); compute in *.
      apply H. trivial.
      destruct H; intuition.
Qed.
(* end hide *)

#[export]
Instance Trichotomous_Ror :
  forall (A : Type) (R S : rel A),
    Trichotomous R -> Trichotomous S -> Trichotomous (Ror R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Trichotomous_Rand :
  exists (A : Type) (R S : rel A),
    Trichotomous R /\ Trichotomous S /\ ~ Trichotomous (Rand R S).
(* begin hide *)
Proof.
  exists nat, lt, gt. split; [idtac | split].
    1-2: split; lia.
    destruct 1 as [H]. unfold Rand in H. specialize (H 0 1).
      decompose [and or] H; clear H.
        inversion H2.
        inversion H1.
        inversion H0.
Qed.
(* end hide *)

(** ** Relacje słabo trychotomiczne *)

Class WeaklyTrichotomous {A : Type} (R : rel A) : Prop :=
{
    weakly_trichotomous : forall x y : A, x <> y -> R x y \/ R y x
}.

#[export]
Instance WeaklyTrichotomous_Total :
  forall (A : Type) (R : rel A),
    Total R -> WeaklyTrichotomous R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance WeaklyTrichotomous_Empty :
  forall R : rel Empty_set, WeaklyTrichotomous R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance WeaklyTrichotomous_unit :
  forall R : rel unit, WeaklyTrichotomous R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance WeaklyTrichotomous_RTrue :
  forall A : Type,
    WeaklyTrichotomous (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_WeaklyTrichotomous_RFalse_two_elems :
  forall {A : Type} {x y : A},
    x <> y -> ~ WeaklyTrichotomous (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance WeaklyTrichotomous_Rinv :
  forall (A : Type) (R : rel A),
    WeaklyTrichotomous R -> WeaklyTrichotomous (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_WeaklyTrichotomous_Rcomp :
  exists (A : Type) (R S : rel A),
    WeaklyTrichotomous R /\ WeaklyTrichotomous S /\ ~ WeaklyTrichotomous (Rcomp R S).
(* begin hide *)
Proof.
  exists nat, lt, lt. split; [| split].
  1-2: split; lia.
  destruct 1 as [H]; unfold Rcomp in H.
  destruct (H 0 1 ltac:(lia)) as [[b Hb] | [b Hb]]; lia.
Qed.
(* end hide *)

Lemma not_WeaklyTrichotomous_Rnot :
  exists (A : Type) (R : rel A),
    WeaklyTrichotomous R /\ ~ WeaklyTrichotomous (Rnot R).
(* begin hide *)
Proof.
  exists bool, RTrue.
  split.
  - rel.
  - intros [H]. specialize (H true false ltac:(congruence)). rel.
Qed.
(* end hide *)

#[export]
Instance WeaklyTrichotomous_Ror :
  forall (A : Type) (R S : rel A),
    WeaklyTrichotomous R -> WeaklyTrichotomous S -> WeaklyTrichotomous (Ror R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_WeaklyTrichotomous_Rand :
  exists (A : Type) (R S : rel A),
    WeaklyTrichotomous R /\ WeaklyTrichotomous S /\ ~ WeaklyTrichotomous (Rand R S).
(* begin hide *)
Proof.
  exists bool, (fun x _ => x = true), (fun x _ => x = false).
  split; [| split].
  - rel. destruct x, y; intuition.
  - rel. destruct x, y; intuition.
  - intros [H].
    specialize (H true false ltac:(congruence)).
    rel.
Qed.
(* end hide *)

(** ** Relacje gęste *)

Class Dense {A : Type} (R : rel A) : Prop :=
{
    dense : forall x y : A, R x y -> exists z : A, R x z /\ R z y
}.

#[export]
Instance Dense_RTrue :
  forall A : Type, Dense (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Dense_RFalse :
  forall A : Type, Dense (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Dense_eq :
  forall A : Type, Dense (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Dense_Reflexive :
  forall {A : Type} (R : rel A),
    Reflexive R -> Dense R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Dense_Rinv :
  forall (A : Type) (R : rel A),
    Dense R -> Dense (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Dense_Rcomp :
  exists (A : Type) (R S : rel A),
    Dense R /\ Dense S /\ ~ Dense (Rcomp R S).
(* begin hide *)
Proof.
  (* TODO: Potrzebna jest dowolna relacja gęsta i antyzwrotna. *)
  exists nat.
  assert (R : rel nat). admit.
  assert (Dense R). admit.
  assert (Antireflexive R). admit.
  exists R, R. split; [assumption | split; [assumption |]].
  destruct 1. unfold Rcomp in *.
Restart.
Abort.
(* end hide *)

Lemma not_Dense_Rnot :
  exists (A : Type) (R : rel A),
    Dense R /\ ~ Dense (Rnot R).
(* begin hide *)
Proof.
  exists bool, eq.
  split.
  - typeclasses eauto.
  - intros [D]; unfold Rnot in D.
    destruct (D true false ltac:(congruence)) as (b & H1 & H2).
    destruct b; congruence.
Qed.
(* end hide *)

#[export]
Instance Dense_Ror :
  forall (A : Type) (R S : rel A),
    Dense R -> Dense S -> Dense (Ror R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Dense_Rand :
  exists (A : Type) (R S : rel A),
    Dense R /\ Dense S /\ ~ Dense (Rand R S).
(* begin hide *)
Proof.
Abort.
(* end hide *)

(** ** Relacje słabozwrotne *)

Class CoReflexive {A : Type} (R : rel A) : Prop :=
{
    coreflexive : forall x y : A, R x y -> x = y;
}.

#[export]
Instance CoReflexive_Empty :
  forall R : rel Empty_set, CoReflexive R.
(* begin hide *)
Proof.
  split; intros [].
Qed.
(* end hide *)

#[export]
Instance CoReflexive_RFalse :
  forall A : Type, CoReflexive (@RFalse A A).
(* begin hide *)
Proof.
  split; intros _ _ [].
Qed.
(* end hide *)

#[export]
Instance CoReflexive_eq :
  forall A : Type, CoReflexive (@eq A).
(* begin hide *)
Proof.
  split; trivial.
Qed.
(* end hide *)

Lemma CoReflexive_subrelation_eq :
  forall {A : Type} {R : rel A},
    CoReflexive R -> subrelation R (@eq A).
(* begin hide *)
Proof.
  intros A R [H] x y. apply H.
Qed.
(* end hide *)

#[export]
Instance CoReflexive_Rinv :
  forall (A : Type) (R : rel A),
    CoReflexive R -> CoReflexive (Rinv R).
(* begin hide *)
Proof.
  intros A R [HR].
  split; unfold Rinv.
  intros x y r.
  symmetry.
  apply HR.
  assumption.
Qed.
(* end hide *)

#[export]
Instance CoReflexive_Rcomp :
  forall (A : Type) (R S : rel A),
    CoReflexive R -> CoReflexive S -> CoReflexive (Rcomp R S).
(* begin hide *)
Proof.
  intros A R S [HR] [HS]; split.
  intros x y (z & r & s).
  rewrite (HR _ _ r), (HS _ _ s).
  reflexivity.
Qed.
(* end hide *)

Lemma not_CoReflexive_Rnot :
  exists (A : Type) (R : rel A),
    CoReflexive R /\ ~ CoReflexive (Rnot R).
(* begin hide *)
Proof.
  exists bool, (fun b1 b2 => b1 = true /\ b2 = true).
  split; [rel |].
  unfold Rnot; intros [WR].
  specialize (WR true false); intuition.
Qed.
(* end hide *)

#[export]
Instance CoReflexive_Ror :
  forall (A : Type) (R S : rel A),
    CoReflexive R -> CoReflexive S -> CoReflexive (Ror R S).
(* begin hide *)
Proof.
  intros A R S [HR] [HS]; split.
  intros x y [r | s].
  - apply HR; assumption.
  - apply HS; assumption.
Qed.
(* end hide *)

#[export]
Instance CoReflexive_Rand_l :
  forall (A : Type) (R S : rel A),
    CoReflexive R -> CoReflexive (Rand R S).
(* begin hide *)
Proof.
  intros A R S [HR]; split.
  intros x y [r s].
  apply HR; assumption.
Qed.
(* end hide *)

#[export]
Instance CoReflexive_Rand_r :
  forall (A : Type) (R S : rel A),
    CoReflexive S -> CoReflexive (Rand R S).
(* begin hide *)
Proof.
  intros A R S [HS]; split.
  intros x y [r s].
  apply HS; assumption.
Qed.
(* end hide *)

#[export]
Instance CoReflexive_LeftUnique :
  forall {A : Type} (R : rel A),
    LeftUnique R -> CoReflexive (Rcomp R (Rinv R)).
(* begin hide *)
Proof.
  intros A R [H].
  split; unfold Rinv.
  intros x y (z & r & r').
  eapply H; eassumption.
Qed.
(* end hide *)

(** ** Relacje cyrkularne *)

Class Circular {A : Type} (R : rel A) : Prop :=
{
    circular : forall x y z : A, R x y -> R y z -> R z x;
}.

#[export]
Instance Circular_Empty :
  forall R : rel Empty_set, Circular R.
(* begin hide *)
Proof.
  split; intros [].
Qed.
(* end hide *)

#[export]
Instance Circular_RTrue :
  forall A : Type, Circular (@RTrue A A).
(* begin hide *)
Proof.
  split; compute. trivial.
Qed.
(* end hide *)

#[export]
Instance Circular_RFalse :
  forall A : Type, Circular (@RFalse A A).
(* begin hide *)
Proof.
  split; intros _ _ _ [].
Qed.
(* end hide *)

#[export]
Instance Circular_eq {A : Type} : Circular (@eq A).
(* begin hide *)
Proof.
  split; congruence.
Qed.
(* end hide *)

Require Import Lia.

#[export]
Instance Circular_Rcomp :
  forall (A : Type) (R S : rel A),
    Circular R -> Circular S -> Circular (Rcomp R S).
(* begin hide *)
Proof.
  intros A R S [HR] [HS]; split; red.
  intros x y z (w1 & r1 & s1) (w2 & r2 & s2).
Abort.
(* end hide *)

#[export]
Instance Circular_Rinv :
  forall (A : Type) (R : rel A),
    Circular R -> Circular (Rinv R).
(* begin hide *)
Proof.
  intros A R [HR].
  split; unfold Rinv.
  intros x y z r1 r2.
  specialize (HR _ _ _ r2 r1).
  assumption.
Qed.
(* end hide *)

Lemma Circular_Rcomp :
  exists (A : Type) (R S : rel A),
    Circular R /\ Circular S /\ ~ Circular (Rcomp R S).
(* begin hide *)
Proof.
  exists nat,
    (fun n m =>
      n = 0 /\ m = 1
        \/
      n = 1 /\ m = 2
        \/
      n = 2 /\ m = 0),
    (fun n m =>
      n = 2 /\ m = 3
        \/
      n = 3 /\ m = 4
        \/
      n = 4 /\ m = 2).
  unfold Rcomp.
  split; [| split].
  - split; lia.
  - split; lia.
  - destruct 1 as [H].
(*     Axiom x y z : nat. *)
    specialize (H 0 2 0). destruct H.
    + exists 2. intuition.
Admitted.
(* end hide *)

Lemma Circular_Ror :
  exists (A : Type) (R S : rel A),
    Circular R /\ Circular S /\ ~ Circular (Ror R S).
(* begin hide *)
Proof.
  exists nat,
    (fun n m =>
      n = 0 /\ m = 1
        \/
      n = 1 /\ m = 2
        \/
      n = 2 /\ m = 0),
    (fun n m =>
      n = 2 /\ m = 3
        \/
      n = 3 /\ m = 4
        \/
      n = 4 /\ m = 2).
  split; [| split].
  - split; lia.
  - split; lia.
  - unfold Ror; destruct 1 as [H].
    specialize (H 1 2 3). specialize (H ltac:(lia) ltac:(lia)).
    intuition; try lia.
Qed.
(* end hide *)

#[export]
Instance Circular_Rand :
  forall (A : Type) (R S : rel A),
    Circular R -> Circular S -> Circular (Rand R S).
(* begin hide *)
Proof.
  intros A R S [HR] [HS]; split.
  intros x y z [r1 s1] [r2 s2].
  split.
  - eapply HR; eassumption.
  - eapply HS; eassumption.
Qed.
(* end hide *)

#[export]
Instance Equivalence_Reflexive_Circular :
  forall {A : Type} (R : rel A),
    Reflexive R -> Circular R -> Equivalence R.
(* begin hide *)
Proof.
  intros A R [HR] [HC].
  split; split.
  - assumption.
  - intros x y r. eapply HC.
    + apply HR.
    + assumption.
  - intros x y z rxy ryx. eapply HC.
    + apply HR.
    + eapply HC; eassumption.
Qed.
(* end hide *)

(** ** Relacje kwazizwrotne *)

(** *** Relacje lewostronnie kwazizwrotne *)

Class LeftQuasiReflexive {A : Type} (R : rel A) : Prop :=
  left_quasireflexive : forall x y : A, R x y -> R x x.

#[export]
Instance LeftQuasiReflexive_Empty :
  forall R : rel Empty_set, LeftQuasiReflexive R.
(* begin hide *)
Proof.
  intros R [].
Qed.
(* end hide *)

#[export]
Instance LeftQuasiReflexive_eq {A : Type} : LeftQuasiReflexive (@eq A).
(* begin hide *)
Proof.
  compute. trivial.
Qed.
(* end hide *)

#[export]
Instance LeftQuasiReflexive_RFalse :
  forall A : Type, LeftQuasiReflexive (@RFalse A A).
(* begin hide *)
Proof.
  compute. trivial.
Qed.
(* end hide *)

#[export]
Instance LeftQuasiReflexive_RTrue :
  forall A : Type, LeftQuasiReflexive (@RTrue A A).
(* begin hide *)
Proof.
  compute. trivial.
Qed.
(* end hide *)

Lemma not_LeftQuasiReflexive_Rcomp :
  exists (A : Type) (R S : rel A),
    LeftQuasiReflexive R /\ LeftQuasiReflexive S /\ ~ LeftQuasiReflexive (Rcomp R S).
(* begin hide *)
Proof.
  exists
    nat,
    (fun n m =>
      n = 0 /\ m = 1
        \/
      n = 0 /\ m = 0),
    (fun n m =>
      n = 1 /\ m = 2
        \/
      n = 1 /\ m = 1).
  unfold LeftQuasiReflexive, Rcomp.
  split; [| split].
  - intuition.
  - intuition.
  - intro H. destruct (H 0 1) as (b & H1 & H2).
    + exists 1. intuition.
    + intuition congruence.
Qed.
(* end hide *)

Lemma not_LeftQuasiReflexive_Rinv :
  exists (A : Type) (R : rel A),
    LeftQuasiReflexive R /\ ~ LeftQuasiReflexive (Rinv R).
(* begin hide *)
Proof.
  unfold LeftQuasiReflexive, Rinv.
  exists nat, (fun n m => Nat.even n = true).
  split.
  - firstorder.
  - intro H. specialize (H 1 0 eq_refl). cbn in H. congruence.
Qed.
(* end hide *)

#[export]
Instance LeftQuasiReflexive_Rand :
  forall (A : Type) (R S : rel A),
    LeftQuasiReflexive R -> LeftQuasiReflexive S -> LeftQuasiReflexive (Rand R S).
(* begin hide *)
Proof.
  unfold LeftQuasiReflexive.
  intros A R S HR HS x y [r s]; red.
  split.
  - eapply HR; eassumption.
  - eapply HS; eassumption.
Qed.
(* end hide *)

#[export]
Instance LeftQuasiReflexive_Ror :
  forall (A : Type) (R S : rel A),
    LeftQuasiReflexive R -> LeftQuasiReflexive S -> LeftQuasiReflexive (Ror R S).
(* begin hide *)
Proof.
  unfold LeftQuasiReflexive.
  intros A R S HR HS x y [r | s]; red.
  - left. eapply HR; eassumption.
  - right. eapply HS; eassumption.
Qed.
(* end hide *)

(** *** Relacje prawostronnie kwazizwrotne *)

Class RightQuasiReflexive {A : Type} (R : rel A) : Prop :=
  right_quasireflexive : forall x y : A, R x y -> R y y.

Lemma RightQuasiReflexive_spec :
  forall {A : Type} (R : rel A),
    RightQuasiReflexive R <-> LeftQuasiReflexive (Rinv R).
(* begin hide *)
Proof.
  unfold LeftQuasiReflexive, RightQuasiReflexive, Rinv.
  split.
  - intros H x y r. eapply H; eassumption.
  - intros H x y r. eapply H; eassumption.
Qed.
(* end hide *)

(** *** Relacje kwazizwrotne *)

Class QuasiReflexive {A : Type} (R : rel A) : Prop :=
{
    QR_LeftQuasiReflexive :> LeftQuasiReflexive R;
    QR_RightQuasiReflexive :> RightQuasiReflexive R;
}.

#[export]
Instance LeftQuasiReflexive_Rinv :
  forall {A : Type} (R : rel A),
    RightQuasiReflexive R -> LeftQuasiReflexive (Rinv R).
(* begin hide *)
Proof.
  compute. eauto.
Qed.
(* end hide *)

#[export]
Instance QuasiReflexive_Empty :
  forall R : rel Empty_set, QuasiReflexive R.
(* begin hide *)
Proof.
  split.
  - typeclasses eauto.
  - rewrite RightQuasiReflexive_spec. typeclasses eauto.
Qed.
(* end hide *)

#[export]
Instance QuasiReflexive_eq {A : Type} : QuasiReflexive (@eq A).
(* begin hide *)
Proof.
  split.
  - typeclasses eauto.
  - red. trivial.
Qed.
(* end hide *)

#[export]
Instance QuasiReflexive_RFalse :
  forall A : Type, QuasiReflexive (@RFalse A A).
(* begin hide *)
Proof.
  split; compute; trivial.
Qed.
(* end hide *)

#[export]
Instance QuasiReflexive_RTrue :
  forall A : Type, QuasiReflexive (@RTrue A A).
(* begin hide *)
Proof.
  split; compute; trivial.
Qed.
(* end hide *)

#[export]
Instance QuasiReflexive_Rcomp :
  forall (A : Type) (R S : rel A),
    QuasiReflexive R -> QuasiReflexive S -> QuasiReflexive (Rcomp R S).
(* begin hide *)
Proof.
  intros A R S [RL RR] [SL SR].
  split; unfold LeftQuasiReflexive, RightQuasiReflexive, Rcomp in *.
Abort.
(* end hide *)

#[export]
Instance QuasiReflexive_Rinv :
  forall (A : Type) (R : rel A),
    QuasiReflexive R -> QuasiReflexive (Rinv R).
(* begin hide *)
Proof.
  intros A R [HL HR].
  split; firstorder.
Qed.
(* end hide *)

#[export]
Instance QuasiReflexive_Rand :
  forall (A : Type) (R S : rel A),
    QuasiReflexive R -> QuasiReflexive S -> QuasiReflexive (Rand R S).
(* begin hide *)
Proof.
  intros A R S [HRL HRR] [HSL HSR].
  split; firstorder.
Qed.
(* end hide *)

#[export]
Instance QuasiReflexive_Ror :
  forall (A : Type) (R S : rel A),
    QuasiReflexive R -> QuasiReflexive S -> QuasiReflexive (Ror R S).
(* begin hide *)
Proof.
  intros A R S [HRL HRR] [HSL HSR].
  split; firstorder.
Qed.
(* end hide *)

(** ** Relacje euklidesowe *)

(** *** Relacje prawostronnie euklidesowe *)

Class RightEuclidean {A : Type} (R : rel A) : Prop :=
  right_euclidean : forall x y z : A, R x y -> R x z -> R y z.

#[export]
Instance RightEuclidean_Empty :
  forall R : rel Empty_set, RightEuclidean R.
(* begin hide *)
Proof.
  intros R [].
Qed.
(* end hide *)

#[export]
Instance RightEuclidean_eq {A : Type} : RightEuclidean (@eq A).
(* begin hide *)
Proof.
  compute. congruence.
Qed.
(* end hide *)

#[export]
Instance RightEuclidean_RFalse :
  forall A : Type, RightEuclidean (@RFalse A A).
(* begin hide *)
Proof.
  compute; trivial.
Qed.
(* end hide *)

#[export]
Instance RightEuclidean_RTrue :
  forall A : Type, RightEuclidean (@RTrue A A).
(* begin hide *)
Proof.
  compute; trivial.
Qed.
(* end hide *)

Lemma not_RightEuclidean_Rcomp :
  exists (A : Type) (R S : rel A),
    RightEuclidean R /\ RightEuclidean S /\ ~ RightEuclidean (Rcomp R S).
(* begin hide *)
Proof.
  exists
    nat,
    (fun n m =>
      n = 0 /\ m = 1
        \/
      n = 1 /\ m = 1),
    (fun n m =>
      n = 1 /\ m = 2
        \/
      n = 2 /\ m = 2).
  split; [| split].
  - red. intuition.
  - red. intuition.
  - unfold RightEuclidean, Rcomp. intro H.
    specialize (H 0 2 2).
    destruct H as (b & H1 & H2).
    + exists 1. intuition.
    + exists 1. intuition.
    + intuition; try congruence.
Qed.
(* end hide *)

Lemma not_RightEuclidean_Rinv :
  exists (A : Type) (R : rel A),
    RightEuclidean R /\ ~ RightEuclidean (Rinv R).
(* begin hide *)
Proof.
  exists
    nat,
    (fun n m =>
      n = 0 /\ m = 1
        \/
      n = 1 /\ m = 1).
  split; compute.
  - firstorder.
  - intro H. specialize (H 1 0 0 ltac:(lia)). intuition congruence.
Qed.
(* end hide *)

#[export]
Instance RightEuclidean_Rand :
  forall (A : Type) (R S : rel A),
    RightEuclidean R -> RightEuclidean S -> RightEuclidean (Rand R S).
(* begin hide *)
Proof.
  unfold RightEuclidean, Rand.
  intros A R S HR HS x y z [r1 s1] [r2 s2].
  split; firstorder.
Qed.
(* end hide *)

Lemma not_RightEuclidean_Ror :
  exists (A : Type) (R S : rel A),
    RightEuclidean R /\ RightEuclidean S /\ ~ RightEuclidean (Ror R S).
(* begin hide *)
Proof.
  exists
    nat,
    (fun n m =>
      n = 0 /\ m = 1
        \/
      n = 1 /\ m = 1),
    (fun n m =>
      n = 0 /\ m = 2
        \/
      n = 2 /\ m = 2).
  firstorder. compute. intro H.
  specialize (H 0 1 2 ltac:(lia) ltac:(lia)). intuition congruence.
Qed.
(* end hide *)

(** *** Relacje lewostronnie Euklidesowe *)

Class LeftEuclidean {A : Type} (R : rel A) : Prop :=
  left_euclidean : forall x y z : A, R y x -> R z x -> R y z.

Lemma RightEuclidean_Rinv :
  forall {A : Type} (R : rel A),
    RightEuclidean (Rinv R) <-> LeftEuclidean R.
(* begin hide *)
Proof.
  intros A R. split; compute; firstorder.
Qed.
(* end hide *)

(** *** Relacje euklidesowe *)

Class Euclidean {A : Type} (R : rel A) : Prop :=
{
    Euclidean_RightEuclidean :> RightEuclidean R;
    Euclidean_LeftEuclidean :> LeftEuclidean R;
}.

#[export]
Instance Euclidean_Empty :
  forall R : rel Empty_set, Euclidean R.
(* begin hide *)
Proof.
  intros R. split; intros [].
Qed.
(* end hide *)

#[export]
Instance Euclidean_eq {A : Type} : Euclidean (@eq A).
(* begin hide *)
Proof.
  split; compute; congruence.
Qed.
(* end hide *)

#[export]
Instance Euclidean_RFalse :
  forall A : Type, Euclidean (@RFalse A A).
(* begin hide *)
Proof.
  split; compute; trivial.
Qed.
(* end hide *)

#[export]
Instance Euclidean_RTrue :
  forall A : Type, Euclidean (@RTrue A A).
(* begin hide *)
Proof.
  split; compute; trivial.
Qed.
(* end hide *)

#[export]
Instance Euclidean_Rcomp :
  forall (A : Type) (R S : rel A),
    Euclidean R -> Euclidean S -> Euclidean (Rcomp R S).
(* begin hide *)
Proof.
  intros A R S [RR RL] [SR SL]; split; compute in *.
  - intros x y z (w1 & r1 & s1) (w2 & r2 & s2).
    assert (R w1 w2) by firstorder.
    assert (R w1 x) by firstorder.
Abort.
(* end hide *)

Lemma not_Euclidean_Rcomp :
  exists (A : Type) (R S : rel A),
    Euclidean R /\ Euclidean S /\ ~ Euclidean (Rcomp R S).
(* begin hide *)
Proof.
  exists
    nat,
    (fun n m => n <= 1 /\ m <= 1),
    (fun n m => 0 < n <= 2 /\ 0 < m <= 2).
  split; [| split].
  - split; compute; intuition.
  - split; compute; intuition.
  - intros [HR HL]; compute in *.
    specialize (HR 0 2 2).
    destruct HR as (b & H1 & H2).
    + exists 1. intuition.
    + exists 1. intuition.
    + intuition; lia.
Qed.
(* end hide *)

#[export]
Instance Euclidean_Rinv :
  forall (A : Type) (R : rel A),
    Euclidean R -> Euclidean (Rinv R).
(* begin hide *)
Proof.
  intros A R [HR HL].
  split; compute in *; firstorder.
Qed.
(* end hide *)

#[export]
Instance Euclidean_Rand :
  forall (A : Type) (R S : rel A),
    Euclidean R -> Euclidean S -> Euclidean (Rand R S).
(* begin hide *)
Proof.
  intros A R S [RR RL] [SR SL].
  split; compute in *; firstorder.
Restart.
  intros A R S [RR RL] [SR SL].
  split.
  - apply RightEuclidean_Rand; assumption.
  - rewrite <- RightEuclidean_Rinv.
Abort.
(* end hide *)

#[export]
Instance Euclidean_Ror :
  forall (A : Type) (R S : rel A),
    Euclidean R -> Euclidean S -> Euclidean (Ror R S).
(* begin hide *)
Proof.
  intros A R S [RR RL] [SR SL].
  split; compute in *. firstorder.
Abort.
(* end hide *)

Lemma not_Euclidean_Ror :
  exists (A : Type) (R S : rel A),
    Euclidean R /\ Euclidean S /\ ~ Euclidean (Ror R S).
(* begin hide *)
Proof.
  exists
    nat,
    (fun n m => n <= 1 /\ m <= 1),
    (fun n m => 22 < n <= 32 /\ 22 < m <= 32).
  split; [| split].
  - split; compute; firstorder.
  - split; compute; firstorder.
  - intros [HR HL]; compute in *.
    specialize (HL 0 1 1 ltac:(lia) ltac:(lia)).
Admitted.
(* end hide *)

(** ** Relacje antyprzechodnie *)

Class Antitransitive {A : Type} (R : rel A) : Prop :=
  antitransitive : forall x y z : A, R x y -> R y z -> ~ R x z.

#[export]
Instance Antitransitive_Empty :
  forall R : rel Empty_set, Antitransitive R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Antitransitive_RTrue_inhabited :
  forall A : Type, A -> ~ Antitransitive (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Antitransitive_RFalse :
  forall A : Type, Antitransitive (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Antitransitive_eq_inhabited :
  forall A : Type, A -> ~ Antitransitive (@eq A).
(* begin hide *)
Proof.
  unfold Antitransitive.
  intros A a H.
  specialize (H a a a eq_refl eq_refl).
  contradiction.
Qed.
(* end hide *)

#[export]
Instance Antitransitive_successor :
  Antitransitive (fun x y => y = S x).
(* begin hide *)
Proof.
  unfold Antitransitive. lia.
Qed.
(* end hide *)

#[export]
Instance Antitransitive_Rinv :
  forall (A : Type) (R : rel A),
    Antitransitive R -> Antitransitive (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Antitransitive_Rcomp :
  exists (A : Type) (R S : rel A),
    Antitransitive R /\ Antitransitive S /\ ~ Antitransitive (Rcomp R S).
(* begin hide *)
Proof.
  unfold Antitransitive, Rcomp.
  exists nat, (fun x y => y = S x), (fun x y => y = S x).
  repeat split; [lia | lia |].
  intros H.
  apply (H 1 3 5).
  - exists 2. lia.
  - exists 4. lia.
  - exists 2.
Abort.
(* end hide *)

Lemma not_Antitransitive_Rnot :
  exists (A : Type) (R : rel A),
    Antitransitive R /\ ~ Antitransitive (Rnot R).
(* begin hide *)
Proof.
  unfold Antitransitive, Rnot.
  exists nat, (fun x y => y = S x).
  split; [lia |].
  intros H.
  apply (H 0 0 0); lia.
Qed.
(* end hide *)

Lemma not_Antitransitive_Ror :
  exists (A : Type) (R S : rel A),
    Antitransitive R /\ Antitransitive S /\ ~ Antitransitive (Ror R S).
(* begin hide *)
Proof.
  exists nat, (fun x y => y = S (S x)), (fun x y => x = S y).
  unfold Antitransitive, Ror.
  repeat split; [lia | lia |].
  intros AT.
Abort.
(* end hide *)

Lemma not_Antitransitive_Rand :
  exists (A : Type) (R S : rel A),
    Antitransitive R /\ Antitransitive S /\ ~ Antitransitive (Rand R S).
(* begin hide *)
Proof.
  unfold Antitransitive, Rand.
  exists nat, lt, lt.
Abort.
(* end hide *)

(** ** Relacje koprzechodnie *)

Class CoTransitive {A : Type} (R : rel A) : Prop :=
  cotransitive : forall {x z : A}, R x z -> forall y : A, R x y \/ R y z.

#[export]
Instance CoTransitive_Empty :
  forall R : rel Empty_set, CoTransitive R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance CoTransitive_RTrue :
  forall A : Type, CoTransitive (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance CoTransitive_RFalse :
  forall A : Type, CoTransitive (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma CoTransitive_eq_unit :
  CoTransitive (@eq unit).
(* begin hide *)
Proof. rel. intuition. Qed.
(* end hide *)

Lemma not_CoTransitive_eq_two_elems :
  forall {A : Type} {x y : A},
    x <> y -> ~ CoTransitive (@eq A).
(* begin hide *)
Proof.
  unfold CoTransitive.
  intros A x y Hneq CT.
  destruct (CT x x eq_refl y); congruence.
Qed.
(* end hide *)

#[export]
Instance CoTransitive_Rinv :
  forall (A : Type) (R : rel A),
    CoTransitive R -> CoTransitive (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_CoTransitive_Rcomp :
  exists (A : Type) (R S : rel A),
    CoTransitive R /\ CoTransitive S /\ ~ CoTransitive (Rcomp R S).
(* begin hide *)
Proof.
  unfold CoTransitive, Rcomp.
  exists nat, lt, lt.
  repeat split; [lia | lia |].
  intros H.
  assert (H012 : exists b : nat, 0 < b < 2) by (exists 1; lia).
  destruct (H 0 2 H012 1) as [[b Hb] | [b Hb]]; lia.
Qed.
(* end hide *)

Lemma not_CoTransitive_Rnot :
  exists (A : Type) (R : rel A),
    CoTransitive R /\ ~ CoTransitive (Rnot R).
(* begin hide *)
Proof.
  unfold CoTransitive, Rnot.
  exists nat, (fun x y => x <> y).
  split; [lia |].
  intros H.
  specialize (H 0 0 ltac:(lia) 1).
  lia.
Qed.
(* end hide *)

#[export]
Instance CoTransitive_Ror :
  forall (A : Type) (R S : rel A),
    CoTransitive R -> CoTransitive S -> CoTransitive (Ror R S).
(* begin hide *)
Proof.
  unfold CoTransitive, Ror.
  intros A R S CTR CTS x y [r | s] z.
  - destruct (CTR _ _ r z); auto.
  - destruct (CTS _ _ s z); auto.
Qed.
(* end hide *)

Lemma not_CoTransitive_Rand :
  exists (A : Type) (R S : rel A),
    CoTransitive R /\ CoTransitive S /\ ~ CoTransitive (Rand R S).
(* begin hide *)
Proof.
  unfold CoTransitive, Rand.
  exists nat, ge, lt.
  repeat split; [lia | lia |].
  intros H.
Abort.
(* end hide *)

(** ** Relacje kwaziprzechodnie *)

Definition SymmetricPart {A : Type} (R : rel A) : rel A :=
  fun x y : A => R x y /\ R y x.

Definition AsymmetricPart {A : Type} (R : rel A) : rel A :=
  fun x y : A => R x y /\ ~ R y x.

Class Quasitransitive {A : Type} (R : rel A) : Prop :=
  quasitransitive :> Transitive (AsymmetricPart R).

#[export]
Instance Symmetric_SymmetricPart :
  forall {A : Type} (R : rel A),
    Symmetric (SymmetricPart R).
(* begin hide *)
Proof.
  intros A R. split; unfold SymmetricPart.
  intros x y [rxy ryx]. split; assumption.
Qed.
(* end hide *)

#[export]
Instance Quasitransitive_Symmetric :
  forall {A : Type} (R : rel A),
    Symmetric R -> Quasitransitive R.
(* begin hide *)
Proof.
  intros A R [HS]; split; unfold AsymmetricPart.
  intros x y z [rxy nryx] [ryz nrzy].
  contradict nryx. apply HS. assumption.
Qed.
(* end hide *)

#[export]
Instance Quasitransitive_Transitive :
  forall {A : Type} (R : rel A),
    Transitive R -> Quasitransitive R.
(* begin hide *)
Proof.
  intros A R [HT]; split; unfold AsymmetricPart.
  intros x y z [rxy nryx] [ryz nrzy]. split.
  - apply HT with y; assumption.
  - intro rzx. contradict nrzy. apply HT with x; assumption.
Qed.
(* end hide *)

Lemma Quasitransitive_char :
  forall {A : Type} (R : rel A),
    Quasitransitive R <-> (R <--> Ror (SymmetricPart R) (AsymmetricPart R)).
(* begin hide *)
Proof.
  assert (LEM : forall P : Prop, P \/ ~ P) by admit.
  split.
  - intros [QT]; unfold Ror, SymmetricPart, AsymmetricPart in *; split.
    + intros x y r. destruct (LEM (R y x)); auto.
    + intros x y [[rxy ryx] | [rxy nryx]]; assumption.
  - intros [HRL _].
    split; unfold same_hrel, subrelation, Ror, SymmetricPart, AsymmetricPart in *.
    intros x y z [rxy nryx] [ryz nrzy].
    destruct (LEM (R x z)).
    + split; [assumption |].
Abort.
(* end hide *)

#[export]
Instance Quasitransitive_Empty :
  forall R : rel Empty_set, Quasitransitive R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Quasitransitive_RTrue :
  forall A : Type, Quasitransitive (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Quasitransitive_RFalse :
  forall A : Type, Quasitransitive (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma Quasitransitive_eq :
  forall A : Type, Quasitransitive (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Quasitransitive_Rinv :
  forall (A : Type) (R : rel A),
    Quasitransitive R -> Quasitransitive (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Quasitransitive_Rcomp :
  exists (A : Type) (R S : rel A),
    Quasitransitive R /\ Quasitransitive S /\ ~ Quasitransitive (Rcomp R S).
(* begin hide *)
Proof.
  unfold Quasitransitive, Rcomp.
  exists nat, eq, (fun x y => x <> y).
  split; [| split]; [rel | rel |].
  intros [HT]; unfold AsymmetricPart in HT.
  specialize (HT 0 1 1).
Abort.
(* end hide *)

#[export]
Instance Quasitransitive_Rnot :
  forall {A : Type} (R : rel A),
    Quasitransitive R -> Quasitransitive (Rnot R).
(* begin hide *)
Proof.
  assert (DNE : forall P : Prop, ~ ~ P -> P) by admit.
  unfold Quasitransitive, Rnot, AsymmetricPart.
  intros A R [HT]; split; intros x y z [nrxy nnryx] [nryz nnrzy].
  apply DNE in nnryx, nnrzy. firstorder.
Admitted.
(* end hide *)

#[export]
Instance Quasitransitive_Rnot_conv :
  forall {A : Type} (R : rel A),
    Quasitransitive (Rnot R) -> Quasitransitive R.
(* begin hide *)
Proof.
  assert (DNE : forall P : Prop, ~ ~ P -> P) by admit.
  unfold Quasitransitive, Rnot, AsymmetricPart.
  intros A R [HT]; split; intros x y z [nrxy nnryx] [nryz nnrzy].
  destruct (HT z y x).
  - auto.
  - auto.
  - apply DNE in H0; auto.
Admitted.
(* end hide *)

#[export]
Instance Quasitransitive_Ror :
  forall (A : Type) (R S : rel A),
    Quasitransitive R -> Quasitransitive S -> Quasitransitive (Ror R S).
(* begin hide *)
Proof.

Abort.
(* end hide *)

#[export]
Instance Quasitransitive_Rand :
  forall {A : Type} (R S : rel A),
    Quasitransitive R -> Quasitransitive S -> Quasitransitive (Rand R S).
(* begin hide *)
Proof.
  unfold Quasitransitive, Rand.
  intros A R S [HR] [HS]; unfold AsymmetricPart in *.
  split; intros x y z [[rxy sxy] n1] [[ryz syz] n2]; split.
  - split.
    + apply HR with y. split; auto. intro ryx.
      assert (H : S x z /\ ~ S z x).
      {
        apply HS with y; auto. split; [assumption |].
Abort.
(* end hide *)

(** ** Relacje apartheidu *)

Class Apartness {A : Type} (R : rel A) : Prop :=
{
    Apartness_Antireflexive :> Antireflexive R;
    Apartness_Symmetric :> Symmetric R;
    Apartness_Cotransitive :> CoTransitive R;
}.

#[export]
Instance Apartness_Empty :
  forall R : rel Empty_set, Apartness R.
(* begin hide *)
Proof.
  split.
  - apply Antireflexive_Empty.
  - apply Symmetric_Empty.
  - apply CoTransitive_Empty.
Qed.
(* end hide *)

Lemma not_Apartness_RTrue :
  forall {A : Type}, A -> ~ Apartness (@RTrue A A).
(* begin hide *)
Proof.
  intros A a [R _ _].
  eapply not_Antireflexive_RTrue_inhabited.
  - exact a.
  - assumption.
Qed.
(* end hide *)

#[export]
Instance Apartness_RFalse :
  forall {A : Type}, Apartness (@RFalse A A).
(* begin hide *)
Proof.
  split.
  - apply Antireflexive_RFalse.
  - apply Symmetric_RFalse.
  - apply CoTransitive_RFalse.
Qed.
(* end hide *)

Lemma not_Apartness_eq :
  forall {A : Type}, A -> ~ Apartness (@eq A).
(* begin hide *)
Proof.
  intros A a [[R] [S] C].
  apply (R a).
  reflexivity.
Qed.
(* end hide *)

From Typonomikon Require Import B4.

Lemma Apartness_neq :
  forall {A : Type}, Apartness (Rnot (@eq A)).
(* begin hide *)
Proof.
  split.
  - typeclasses eauto.
  - apply Symmetric_Rnot, Symmetric_eq.
  - unfold Rnot. intros x y p z.
    cut (~ ~ (x <> z \/ z <> y)); cycle 1.
    + intro H. apply H. left; intro q. subst.
      apply H. right. assumption.
    + left; intro q. subst. apply H. intro. destruct H0.
      * apply H0. reflexivity.
      * apply p.
Abort.
(* end hide *)

Lemma Apartnes_neq :
  (forall {A : Type}, Apartness (Rnot (@eq A))) ->
    (forall {A : Type} (x y : A), x <> y \/ ~ x <> y).
(* begin hide *)
Proof.
  unfold Rnot.
  intros H A x y.
  destruct (H A) as [[R] [S] C].
  right; intro p.
  specialize (C _ _ p).
Abort.
(* end hide *)

#[export]
Instance Apartness_Rinv :
  forall (A : Type) (R : rel A),
    Apartness R -> Apartness (Rinv R).
(* begin hide *)
Proof.
  unfold Rinv. intros A R [[Anti] [Sym] CoTrans].
  split; [split | split | unfold CoTransitive in *]; intros * H.
  - eapply Anti. eassumption.
  - apply Sym. assumption.
  - intros y. destruct (CoTrans _ _ H y); [right | left]; assumption.
Qed.
(* end hide *)

Lemma not_Apartness_Rcomp :
  exists (A : Type) (R S : rel A),
    Apartness R /\ Apartness S /\ ~ Apartness (Rcomp R S).
(* begin hide *)
Proof.
  pose (R := fun b1 b2 => b1 = negb b2).
  assert (H' : Apartness R).
  {
    unfold R. split.
    - split. destruct x; inversion 1.
    - split. intros x y ->. destruct y; reflexivity.
    - intros x y -> z. destruct y, z; intuition.
  }
  exists bool, R, R.
  split; [| split]; [assumption | assumption |].
  unfold Rcomp, R.
  destruct 1 as [[A] _ _].
  apply A with true.
  exists false; cbn.
  intuition.
Qed.
(* end hide *)

Lemma not_Apartness_Rnot :
  exists (A : Type) (R : rel A),
    Apartness R /\ ~ Apartness (Rnot R).
(* begin hide *)
Proof.
  exists nat, (Rnot eq).
  split.
  - unfold Rnot; split; [split | split | unfold CoTransitive]; lia.
  - intros [[HA] [HS] HC]; unfold Rnot in *.
    apply (HA 0). lia.
Qed.
(* end hide *)

#[export]
Instance Apartness_Ror :
  forall (A : Type) (R S : rel A),
    Apartness R -> Apartness S -> Apartness (Ror R S).
(* begin hide *)
Proof.
  intros A R S [[RA] [RS] RC] [[SA] [SS] SC].
  unfold Ror; split.
  - split; intros x [r | s].
    + eapply RA. eassumption.
    + eapply SA. eassumption.
  - split. intuition.
  - intros x y [r | s] z.
    + destruct (RC _ _ r z); auto.
    + destruct (SC _ _ s z); auto.
Qed.
(* end hide *)

Lemma not_Rand_Apartness :
  exists (A : Type) (R S : rel A),
    Apartness R /\ Apartness S /\ ~ Apartness (Rand R S).
(* begin hide *)
Proof.
  exists
    (list (nat * nat)),
    (fun l1 l2 => map fst l1 <> map fst l2),
    (fun l1 l2 => map snd l1 <> map snd l2).
  split; [| split].
  - repeat split; unfold CoTransitive; repeat intro.
    + congruence.
    + congruence.
    + destruct (list_eq_dec Nat.eq_dec (map fst x) (map fst y)); subst.
      * rewrite <- e. right. assumption.
      * left. assumption.
  - repeat split; repeat intro.
    + congruence.
    + congruence.
    + destruct (list_eq_dec Nat.eq_dec (map snd x) (map snd y)); subst.
      * rewrite <- e. right. assumption.
      * left. assumption.
  - intros [[A] [S] C]; unfold CoTransitive, Rand in C.
    specialize (C [(1, 2)] [(2, 1)]); cbn in C.
    specialize (C ltac:(split; cbn in *; congruence) [(2, 2)]); cbn in C.
    decompose [and or] C; clear C; congruence.
Qed.
(* end hide *)

(** ** Relacje spójne *)

Class Connected {A : Type} (R : rel A) : Prop :=
{
    connected : forall x y : A, ~ R x y /\ ~ R y x -> x = y;
}.

#[export]
Instance Connected_Total :
  forall (A : Type) (R : rel A),
    Total R -> Connected R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Connected_Empty :
  forall R : rel Empty_set, Connected R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Connected_unit :
  forall R : rel unit, Connected R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Connected_RTrue :
  forall A : Type,
    Connected (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Connected_RFalse_two_elems :
  forall {A : Type} {x y : A},
    x <> y -> ~ Connected (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Connected_Rinv :
  forall (A : Type) (R : rel A),
    Connected R -> Connected (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Connected_Rcomp :
  exists (A : Type) (R S : rel A),
    Connected R /\ Connected S /\ ~ Connected (Rcomp R S).
(* begin hide *)
Proof.
  exists nat, lt, lt. split; [| split].
  1-2: split; lia.
  destruct 1 as [H]; unfold Rcomp in H.
  specialize (H 0 1).
  assert (~ (exists b : nat, 0 < b < 1) /\ ~ (exists b : nat, 1 < b < 0)).
  {
    split.
    - intros [b Hb]. lia.
    - intros [b Hb]. lia.
  }
  specialize (H H0). congruence.
Qed.
(* end hide *)

Lemma not_Connected_Rnot :
  exists (A : Type) (R : rel A),
    Connected R /\ ~ Connected (Rnot R).
(* begin hide *)
Proof.
  exists bool, RTrue.
  split.
  - rel.
  - intros [H]; compute in H.
    specialize (H true false ltac:(intuition)).
    congruence.
Qed.
(* end hide *)

#[export]
Instance Connected_Ror :
  forall (A : Type) (R S : rel A),
    Connected R -> Connected S ->
      Connected (Ror R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Connected_Rand :
  exists (A : Type) (R S : rel A),
    Connected R
      /\
    Connected S
      /\
    ~ Connected (Rand R S).
(* begin hide *)
Proof.
  exists bool, (fun x _ => x = true), (fun x _ => x = false).
  split; [| split].
  - rel. destruct x, y; intuition.
  - rel. destruct x, y; intuition.
  - intros [H]; compute in H.
    specialize (H true false ltac:(intuition)).
    congruence.
Qed.
(* end hide *)

(** ** Ostre porządki *)

Class StrictPreorder {A : Type} (R : rel A) : Prop :=
{
    StrictPreorder_Antireflexive :> Antireflexive R;
    StrictPreorder_CoTransitive :> CoTransitive R;
}.

Class StrictPartialOrder {A : Type} (R : rel A) : Prop :=
{
    StrictPartialOrder_Preorder :> StrictPreorder R;
    StrictPartialOrder_Antisymmetric :> Antisymmetric R;
}.

Class StrictTotalOrder {A : Type} (R : rel A) : Prop :=
{
    StrictTotalOrder_PartialOrder :> StrictPartialOrder R;
    StrictTotalOrder_Connected : Connected R;
}.

Class Quasiorder {A : Type} (R : rel A) : Prop :=
{
    Quasiorder_Antireflexive :> Antireflexive R;
    Quasiorder_Transitive :> Transitive R;
}.

(** ** Relacje słabo ekstensjonalne *)

Class WeaklyExtensional {A : Type} (R : rel A) : Prop :=
{
    weakly_extensional : forall x y : A, (forall t : A, R t x <-> R t y) -> x = y;
}.

Lemma WeaklyExtensional_lt :
  WeaklyExtensional lt.
(* begin hide *)
Proof.
  split; intros x y H.
  cut (~ x < y /\ ~ y < x); [lia |].
  rewrite <- (H x), (H y).
  lia.
Qed.
(* end hide *)

Lemma WeaklyExtensional_le :
  WeaklyExtensional le.
(* begin hide *)
Proof.
  split; intros x y H.
  cut (x <= y /\ y <= x); [lia |].
  rewrite <- (H x), (H y).
  lia.
Qed.
(* end hide *)

Lemma WeaklyExtensional_gt :
  WeaklyExtensional gt.
(* begin hide *)
Proof.
  split; intros x y H.
  cut (~ x < y /\ ~ y < x); [lia |].
  rewrite <- (H x), (H y).
  lia.
Qed.
(* end hide *)

Lemma WeaklyExtensional_ge :
  WeaklyExtensional ge.
(* begin hide *)
Proof.
  split; intros x y H.
  cut (x <= y /\ y <= x); [lia |].
  rewrite <- (H x), (H y).
  lia.
Qed.
(* end hide *)

Lemma not_WeaklyExtensional_RTrue :
  exists A : Type,
    ~ WeaklyExtensional (@RTrue A A).
(* begin hide *)
Proof.
  exists bool.
  intros [WE]; unfold RTrue in *.
  assert (bool -> True <-> True) by intuition.
  specialize (WE true false H).
  congruence.
Qed.
(* end hide *)

Lemma not_WeaklyExtensional_RFalse :
  exists A : Type,
    ~ WeaklyExtensional (@RFalse A A).
(* begin hide *)
Proof.
  exists bool.
  intros [WE]; unfold RFalse in *.
  assert (bool -> False <-> False) by intuition.
  specialize (WE true false H).
  congruence.
Qed.
(* end hide *)

Lemma WeaklyExtensional_Rid :
  forall A : Type,
    WeaklyExtensional (@eq A).
(* begin hide *)
Proof.
  split; compute.
  intros x y H.
  destruct (H x) as [Heq _].
  apply Heq. reflexivity.
Qed.
(* end hide *)

Lemma not_WeaklyExtensional_Rinv :
  exists (A : Type) (R : rel A),
    WeaklyExtensional R /\ ~ WeaklyExtensional (Rinv R).
(* begin hide *)
Proof.
  exists
    comparison,
    (fun x y =>
      x = Eq /\ y = Lt
        \/
      x = Eq /\ y = Gt).
  split; [split |].
(*   - intros x y H. destruct x, y; try reflexivity.
    + specialize (H true). intuition.
    + specialize (H true). intuition. *)
  - intros x y H. specialize (H Eq).
Abort.
(* end hide *)

Lemma not_WeaklyExtensional_Rcomp :
  exists (A : Type) (R S : rel A),
    WeaklyExtensional R /\ WeaklyExtensional S /\ ~ WeaklyExtensional (Rcomp R S).
(* begin hide *)
Proof.
  exists nat, lt, lt.
  repeat split.
  1-2: apply WeaklyExtensional_lt.
  intros [WE]; unfold Rcomp in WE.
  cut (0 = 1); [congruence |]. (* TODO: opisać taktykę [enough] *)
  apply WE. split.
  - intros (b & H1 & H2). lia.
  - intros (b & H1 & H2). lia.
Qed.
(* end hide *)

Lemma not_WeaklyExtensional_Rnot :
  exists (A : Type) (R : rel A),
    WeaklyExtensional R /\ ~ WeaklyExtensional (Rnot R).
(* begin hide *)
Proof.
  exists
    bool,
    (fun x y => x = false \/ y = true).
  repeat split.
  - intros x y H.
    specialize (H true) as Ht.
    specialize (H false) as Hf.
    destruct x, y; intuition.
  - intros [WE]; unfold Rnot in WE.
    specialize (WE true false).
Abort.
(* end hide *)

Lemma not_WeaklyExtensional_Ror :
  exists (A : Type) (R S : rel A),
    WeaklyExtensional R /\ WeaklyExtensional S /\ ~ WeaklyExtensional (Ror R S).
(* begin hide *)
Proof.
  exists nat, lt, ge.
  repeat split.
  - apply WeaklyExtensional_lt.
  - apply WeaklyExtensional_ge.
  - intros [WE]; unfold Ror in WE.
    cut (1 = 2); [lia |].
    apply WE. lia.
Qed.
(* end hide *)

Lemma not_WeaklyExtensional_Rand :
  exists (A : Type) (R S : rel A),
    WeaklyExtensional R /\ WeaklyExtensional S /\ ~ WeaklyExtensional (Rand R S).
(* begin hide *)
Proof.
  exists nat, lt, ge.
  repeat split.
  - apply WeaklyExtensional_lt.
  - apply WeaklyExtensional_ge.
  - intros [WE]; unfold Rand in WE.
    cut (1 = 2); [lia |].
    apply WE. lia.
Qed.
(* end hide *)

(** ** Relacje dobrze ufundowane *)

Class WellFounded {A : Type} (R : rel A) : Prop :=
  well_founded : forall x : A, Acc R x.

CoInductive Inaccessible {A : Type} (R : rel A) (x : A) : Prop :=
{
    inaccessible : exists y : A, R y x /\ Inaccessible R y
}.

Class IllFounded {A : Type} (R : rel A) : Prop :=
  ill_founded : exists x : A, Inaccessible R x.

Lemma not_IllFounded_WellFounded :
  forall {A : Type} (R : rel A),
    WellFounded R -> IllFounded R -> False.
(* begin hide *)
Proof.
  unfold WellFounded, IllFounded.
  intros A R WF [x IA]; revert IA.
  specialize (WF x).
  induction WF as [x H IH].
  intros [(y & r & IA')].
  apply (IH y); assumption.
Qed.
(* end hide *)

#[export]
Instance WellFounded_Empty :
  forall R : rel Empty_set, WellFounded R.
(* begin hide *)
Proof.
  intros R [].
Qed.
(* end hide *)

Lemma not_IllFounded_Empty :
  forall R : rel Empty_set, ~ IllFounded R.
(* begin hide *)
Proof.
  intros R [[]].
Qed.
(* end hide *)

Lemma IllFounded_RTrue_inhabited :
  forall A : Type, A -> IllFounded (@RTrue A A).
(* begin hide *)
Proof.
  unfold IllFounded, RTrue.
  intros A x. exists x.
  cofix CH.
  constructor. exists x.
  split; [trivial | assumption].
Qed.
(* end hide *)

Lemma not_WellFounded_RTrue_inhabited :
  forall A : Type, A -> ~ WellFounded (@RTrue A A).
(* begin hide *)
Proof.
  intros A x WF.
  eapply not_IllFounded_WellFounded; [eassumption |].
  apply IllFounded_RTrue_inhabited; assumption.
Qed.
(* end hide *)

#[export]
Instance WellFounded_RFalse :
  forall A : Type, WellFounded (@RFalse A A).
(* begin hide *)
Proof.
  unfold WellFounded, RFalse.
  intros A x.
  constructor.
  intros y [].
Qed.
(* end hide *)

Lemma not_IllFounded_RFalse :
  forall A : Type, ~ IllFounded (@RFalse A A).
(* begin hide *)
Proof.
  unfold IllFounded, RFalse.
  intros A [x [(y & [] & IA)]].
Qed.
(* end hide *)

#[export]
Instance IllFounded_eq :
  forall A : Type, A -> IllFounded (@eq A).
(* begin hide *)
Proof.
  unfold IllFounded.
  intros A x; exists x.
  unfold WellFounded.
  cofix CH.
  constructor; exists x.
  split; [reflexivity | assumption].
Qed.
(* end hide *)

Lemma not_WellFounded_eq :
  forall A : Type, A -> ~ WellFounded (@eq A).
(* begin hide *)
Proof.
  intros A x WF.
  eapply not_IllFounded_WellFounded; [eassumption |].
  apply IllFounded_eq; assumption.
Qed.
(* end hide *)

#[export]
Instance WellFounded_lt :
  WellFounded lt.
(* begin hide *)
Proof.
  unfold WellFounded.
  induction x as [| n'].
  + constructor. inversion 1.
  + constructor. inversion 1; subst.
    * assumption.
    * apply IHn'. lia.
Qed.
(* end hide *)

#[export]
Instance IllFounded_le :
  IllFounded le.
(* begin hide *)
Proof.
  unfold IllFounded.
  cut (forall n : nat, Inaccessible le n).
  - intros. exists 0. apply H.
  - intros n.
    cofix CH.
    constructor. exists n. split; [lia | assumption].
Qed.
(* end hide *)

#[export]
Instance IllFounded_ge :
  IllFounded ge.
(* begin hide *)
Proof.
  unfold IllFounded.
  cut (forall n : nat, Inaccessible ge n).
  - intros. exists 0. apply H.
  - intros n.
    cofix CH.
    constructor. exists n. split; [lia | assumption].
Qed.
(* end hide *)

#[export]
Instance IllFounded_gt :
  IllFounded gt.
(* begin hide *)
Proof.
  unfold IllFounded.
  cut (forall n : nat, Inaccessible gt n).
  - intros. exists 0. apply H.
  - cofix CH.
    constructor; exists (S n).
    split; [lia | apply CH].
Qed.
(* end hide *)

Lemma not_WellFounded_Rinv :
  exists (A : Type) (R : rel A),
    WellFounded R /\ ~ WellFounded (Rinv R).
(* begin hide *)
Proof.
  exists nat, lt.
  split; [apply lt_wf |].
  intros WF.
  eapply not_IllFounded_WellFounded; [eassumption |].
  unfold Rinv. fold gt.
  apply IllFounded_gt.
Qed.
(* end hide *)

Lemma not_IllFounded_Rinv :
  exists (A : Type) (R : rel A),
    IllFounded R /\ ~ IllFounded (Rinv R).
(* begin hide *)
Proof.
  exists nat, gt.
  split; [apply IllFounded_gt | intros IlF].
  eapply not_IllFounded_WellFounded; [| eassumption].
  unfold Rinv, gt.
  apply WellFounded_lt.
Qed.
(* end hide *)

#[export]
Instance WellFounded_Rcomp :
  forall (A : Type) (R S : rel A),
    WellFounded R -> WellFounded S -> WellFounded (Rcomp R S).
(* begin hide *)
Proof.
  unfold WellFounded, Rcomp.
  intros A R S WFR WFS x.
  specialize (WFR x); revert WFS.
  induction WFR as [x H IH]; intros.
  constructor; intros y (b & r & s).
  apply IH.
Abort.
(* end hide *)

Lemma not_WellFounded_Rcomp :
  exists (A : Type) (R S : rel A),
    WellFounded R /\ WellFounded S /\ IllFounded (Rcomp R S).
(* begin hide *)
Proof.
  exists nat, lt, lt.
  unfold WellFounded.
  split; [| split]; [apply WellFounded_lt | apply WellFounded_lt |].
  - cut (forall n : nat, Inaccessible (Rcomp lt lt) (1 + n)); unfold Rcomp.
Abort.
(* end hide *)

Lemma not_IllFounded_Rcomp :
  exists (A : Type) (R S : rel A),
    IllFounded R /\ IllFounded S /\ ~ IllFounded (Rcomp R S).
(* begin hide *)
Proof.
  exists nat, le, ge.
  split; [| split]; unfold IllFounded.
Abort.
(* end hide *)

Lemma not_WellFounded_Rnot :
  exists (A : Type) (R : rel A),
    WellFounded R /\ ~ WellFounded (Rnot R).
(* begin hide *)
Proof.
  exists nat, lt.
  split; [apply WellFounded_lt | intros WF].
  eapply not_IllFounded_WellFounded; [eassumption |].
  unfold IllFounded, Rnot.
  cut (forall n : nat, Inaccessible (fun a b => ~ a < b) n).
  - intros IlF. exists 0. apply IlF.
  - cofix CH.
    constructor. exists (S n). split; [lia |]. apply CH.
Qed.
(* end hide *)

Lemma not_IllFounded_Rnot :
  exists (A : Type) (R : rel A),
    IllFounded R /\ ~ IllFounded (Rnot R).
(* begin hide *)
Proof.
  exists nat, ge.
  split; [apply IllFounded_ge |].
  intros IlF.
  eapply not_IllFounded_WellFounded; [| eassumption].
  unfold WellFounded, Rnot, ge.
  induction x as [| n'].
  + constructor. lia.
  + constructor. intros y H.
    assert (Hlt : y < S n') by lia; clear H. inversion Hlt; subst.
    * assumption.
    * apply IHn'. lia.
Qed.
(* end hide *)

Lemma not_WellFounded_Ror :
  exists (A : Type) (R S : rel A),
    WellFounded R /\ WellFounded S /\ ~ WellFounded (Ror R S).
(* begin hide *)
Proof.
  exists
    (nat * nat)%type,
    (fun x y => fst x < fst y),
    (fun x y => snd x < snd y).
  split; [| split]; unfold WellFounded, Ror.
  - admit.
  - admit.
  - intros WF. specialize (WF (1, 1)). inversion WF. cbn in *.
    induction WF; subst; cbn in *.
    specialize (H (0, 0) ltac:(cbn; lia)). inversion H.
Abort.
(* end hide *)

#[export]
Instance WellFounded_Rand :
  forall (A : Type) (R S : rel A),
    WellFounded R -> WellFounded S -> WellFounded (Rand R S).
(* begin hide *)
Proof.
  unfold WellFounded, Rand.
  intros A R S WFR WFS x.
  specialize (WFR x).
  induction WFR as [x Hlt IH].
  constructor; intros y [r s].
  apply IH; assumption.
Qed.
(* end hide *)

Lemma not_IllFounded_Ror :
  exists (A : Type) (R S : rel A),
    IllFounded R /\ IllFounded S /\ ~ IllFounded (Ror R S).
(* begin hide *)
Proof.
  exists
    (nat * nat)%type,
    (fun x y => fst x < fst y),
    (fun x y => snd x < snd y).
  split; [| split]; unfold IllFounded, Ror.
  - admit.
  - admit.
  - intros WF.
Abort.
(* end hide *)

#[export]
Instance IllFounded_Rand :
  forall (A : Type) (R S : rel A),
    IllFounded R -> IllFounded S -> IllFounded (Rand R S).
(* begin hide *)
Proof.
  unfold IllFounded, Rand.
Abort.
(* end hide *)

(** ** Dobre porządki *)

(* begin hide *)
Class WellPreorder {A : Type} (R : rel A) : Prop :=
{
    WellPreorder_StrictPreorder :> StrictPreorder R;
    WellPreorder_WellFounded :> WellFounded R;
    WellPreorder_WeaklyExtensional :> WeaklyExtensional R;
}.

Class WellPartialOrder {A : Type} (R : rel A) : Prop :=
{
    WellPartialOrder_StrictPartialOrder :> StrictPartialOrder R;
    WellPartialOrder_WellFounded :> WellFounded R;
    WellPartialOrder_WeaklyExtensional :> WeaklyExtensional R;
}.

Class WellQuasiorder {A : Type} (R : rel A) : Prop :=
{
    WellQuasiorder_Quasiorder :> Quasiorder R;
    WellQuasiorder_WellFounded :> WellFounded R;
    WellQuasiorder_WeaklyExtensional :> WeaklyExtensional R;
}.
(* Class WellOrder {A : Type} (R : rel A) : Prop :=
{
    WellOrder_PartialOrder :> StrictTotalOrder R;
    WellOrder_WellFounded :> WellFounded R;
    WellOrder_WeaklyExtensional :> WeaklyExtensional R;
}. *)
(* end hide *)

Class WellOrder {A : Type} (R : rel A) : Prop :=
{
    WellOrder_Transitive :> Transitive R;
    WellOrder_WellFounded :> WellFounded R;
    WellOrder_WeaklyExtensional :> WeaklyExtensional R;
}.

#[export]
Instance Antisymmetric_WellOrder :
  forall {A : Type} (R : rel A),
    WellOrder R -> Antisymmetric R.
(* begin hide *)
Proof.
  intros A R [[HT] HWF [HWE]]; split; intros x y rxy ryx.
  assert (rxx : R x x) by (eapply HT; eassumption).
  assert (HIlF : IllFounded R). (* TODO: zrobić z tego lemat *)
  {
    red. exists x. cofix CH. constructor. exists x. split; assumption.
  }
  apply not_IllFounded_WellFounded with R; assumption.
Qed.
(* end hide *)

#[export]
Instance Total_WellOrder :
  (forall P : Prop, P \/ ~ P) ->
    forall {A : Type} (R : rel A),
      WellOrder R -> Total R.
(* begin hide *)
Proof.
  intros LEM A R [[HT] HWF [HWE]]; split; intros x y.
  destruct (LEM (R x y)) as [| nrxy]; [left; assumption |].
  destruct (LEM (R y x)) as [| nryx]; [right; assumption |].
  assert (x <> y) by admit.
  assert (exists t : A, ~ (R t x <-> R t y)) as [t Ht] by admit.
  Print Connected.
Abort.
(* end hide *)

(** * Zależności między różnymi rodzajami relacji *)

Lemma Reflexive_from_Symmetric_Transitive_RightTotal :
  forall {A : Type} (R : rel A),
    Symmetric R -> Transitive R -> RightTotal R -> Reflexive R.
(* begin hide *)
Proof.
  intros A R [HS] [HT] [HRT].
  split; intros x.
  destruct (HRT x) as [y r].
  apply HT with y.
  - apply HS. assumption.
  - assumption.
Qed.
(* end hide *)

#[export]
Instance Transitive_CoReflexive :
  forall {A : Type} (R : rel A),
    CoReflexive R -> Transitive R.
(* begin hide *)
Proof.
  intros A R [HC].
  split; intros x y z rxy ryz.
  apply HC in rxy; subst. assumption.
Qed.
(* end hide *)

#[export]
Instance Symmetric_CoReflexive :
  forall {A : Type} (R : rel A),
    CoReflexive R -> Symmetric R.
(* begin hide *)
Proof.
  intros A R [HC].
  split; intros x y r.
  rewrite (HC _ _ r) in r |- *. assumption.
Qed.
(* end hide *)

#[export]
Instance LeftEuclidean_CoReflexive :
  forall {A : Type} (R : rel A),
    CoReflexive R -> LeftEuclidean R.
(* begin hide *)
Proof.
  intros A R [HC] x y z ryx rzx.
  rewrite (HC _ _ rzx) in rzx |- *. assumption.
Qed.
(* end hide *)

#[export]
Instance RightEuclidean_CoReflexive :
  forall {A : Type} (R : rel A),
    CoReflexive R -> RightEuclidean R.
(* begin hide *)
Proof.
  intros A R [HC] x y z rxy rxz.
  rewrite <- (HC _ _ rxy) in rxy |- *. assumption.
Qed.
(* end hide *)

#[export]
Instance Quasitransitive_LeftEuclidean :
  forall {A : Type} (R : rel A),
    LeftEuclidean R -> Quasitransitive R.
(* begin hide *)
Proof.
  intros A R HLE.
  split; unfold LeftEuclidean, AsymmetricPart in *.
  intros x y z [rxy nryx] [ryz nrzy].
Restart.
  intros A R HLE.
  split; unfold LeftEuclidean, AsymmetricPart in *.
  intros x y z [rxy nryx] [ryz nrzy]. split.
  - 
Abort.
(* end hide *)

#[export]
Instance Quasitransitive_RightEuclidean :
  forall {A : Type} (R : rel A),
    RightEuclidean R -> Quasitransitive R.
(* begin hide *)
Proof.
  intros A R HRE.
  split; unfold RightEuclidean, AsymmetricPart in *.
  intros x y z [rxy nryx] [ryz nrzy].
  rel.
Abort.
(* end hide *)

#[export]
Instance LeftQuasiReflexive_CoReflexive :
  forall {A : Type} (R : rel A),
    CoReflexive R -> LeftQuasiReflexive R.
(* begin hide *)
Proof.
  intros A R [HWR] x y r.
  rewrite <- (HWR _ _ r) in r. assumption.
Qed.
(* end hide *)

#[export]
Instance RightQuasiReflexive_CoReflexive :
  forall {A : Type} (R : rel A),
    CoReflexive R -> RightQuasiReflexive R.
(* begin hide *)
Proof.
  intros A R [HWR] x y r.
  rewrite (HWR _ _ r) in r. assumption.
Qed.
(* end hide *)

#[export]
Instance QuasiReflexive_CoReflexive :
  forall {A : Type} (R : rel A),
    CoReflexive R -> QuasiReflexive R.
(* begin hide *)
Proof.
  split; typeclasses eauto.
Qed.
(* end hide *)

#[export]
Instance LeftQuasiReflexive_Reflexive :
  forall {A : Type} (R : rel A),
    Reflexive R -> LeftQuasiReflexive R.
(* begin hide *)
Proof.
  intros A R [HR] x y r. apply HR.
Qed.
(* end hide *)

#[export]
Instance Dense_LeftQuasiReflexive :
  forall {A : Type} (R : rel A),
    LeftQuasiReflexive R -> Dense R.
(* begin hide *)
Proof.
  unfold LeftQuasiReflexive.
  intros A R HLQR; split; intros x y r.
  exists x. split; [| assumption].
  apply HLQR with y; assumption.
Qed.
(* end hide *)

#[export]
Instance Dense_RightQuasiReflexive :
  forall {A : Type} (R : rel A),
    RightQuasiReflexive R -> Dense R.
(* begin hide *)
Proof.
  unfold RightQuasiReflexive.
  intros A R HRQR; split; intros x y r.
  exists y. split; [assumption |].
  apply HRQR with x; assumption.
Qed.
(* end hide *)

#[export]
Instance RightQuasiReflexive_Reflexive :
  forall {A : Type} (R : rel A),
    Reflexive R -> RightQuasiReflexive R.
(* begin hide *)
Proof.
  intros A R [HR] x y r. apply HR.
Qed.
(* end hide *)

#[export]
Instance QuasiReflexive_Reflexive :
  forall {A : Type} (R : rel A),
    Reflexive R -> QuasiReflexive R.
(* begin hide *)
Proof.
  intros A R HR; split; typeclasses eauto.
Qed.
(* end hide *)

#[export]
Instance LeftTotal_Reflexive :
  forall {A : Type} (R : rel A),
    Reflexive R -> LeftTotal R.
(* begin hide *)
Proof.
  intros A R [HR]; split; intros x.
  exists x. apply HR.
Qed.
(* end hide *)

#[export]
Instance RightTotal_Reflexive :
  forall {A : Type} (R : rel A),
    Reflexive R -> RightTotal R.
(* begin hide *)
Proof.
  intros A R [HR]; split; intros x.
  exists x. apply HR.
Qed.
(* end hide *)

#[export]
Instance WeaklyAntisymmetric_CoReflexive :
  forall {A : Type} (R : rel A),
    CoReflexive R -> WeaklyAntisymmetric R.
(* begin hide *)
Proof.
  intros A R [WR]; split; intros x y rxy ryx.
  apply WR. assumption.
Qed.
(* end hide *)

#[export]
Instance WeaklyAntisymmetric_Antisymmetric :
  forall {A : Type} (R : rel A),
    Antisymmetric R -> WeaklyAntisymmetric R.
(* begin hide *)
Proof.
  intros A R [HA]; split; intros x y rxy ryx.
  apply HA in rxy. contradiction.
Qed.
(* end hide *)

#[export]
Instance Antireflexive_Antisymmetric :
  forall {A : Type} (R : rel A),
    Antisymmetric R -> Antireflexive R.
(* begin hide *)
Proof.
  intros A R [HAS]; split; intros x nr.
  eapply HAS; eassumption.
Qed.
(* end hide *)

#[export]
Instance Antireflexive_Antitransitive :
  forall {A : Type} (R : rel A),
    Antitransitive R -> Antireflexive R.
(* begin hide *)
Proof.
  unfold Antitransitive.
  intros A R HAT; split; intros x r.
  apply (HAT x x x); assumption.
Qed.
(* end hide *)

#[export]
Instance Antisymmetric_CoReflexive :
  forall {A : Type} (R : rel A),
    CoReflexive R -> Antisymmetric R.
(* begin hide *)
Proof.
  intros A R [WR]; split; intros x y rxy ryx.
Abort.
(* end hide *)

#[export]
Instance LeftUnique_CoReflexive :
  forall {A : Type} (R : rel A),
    CoReflexive R -> LeftUnique R.
(* begin hide *)
Proof.
  intros A R [CR]; split; intros x1 x2 y rx1y rx2y.
  rewrite (CR _ _ rx1y), (CR _ _ rx2y). reflexivity.
Qed.
(* end hide *)

#[export]
Instance RightUnique_CoReflexive :
  forall {A : Type} (R : rel A),
    CoReflexive R -> RightUnique R.
(* begin hide *)
Proof.
  intros A R [CR]; split; intros x y1 y2 rxy1 rxy2.
  rewrite <- (CR _ _ rxy1), <- (CR _ _ rxy2). reflexivity.
Qed.
(* end hide *)






#[export]
Instance CoReflexive_Symmetric_WeaklyAntisymmetric :
  forall {A : Type} (R : rel A),
    Symmetric R -> WeaklyAntisymmetric R -> CoReflexive R.
(* begin hide *)
Proof.
  intros A R [HS] [HWR]; split; intros x y r.
  apply HWR; [assumption |]. apply HS. assumption.
Qed.
(* end hide *)

Lemma CoReflexive_spec :
  forall {A : Type} (R : rel A),
    CoReflexive R <-> Symmetric R /\ WeaklyAntisymmetric R.
(* begin hide *)
Proof.
  split; [split | destruct 1]; typeclasses eauto.
Qed.
(* end hide *)

Lemma eq_greatest_Symmetric_WeaklyAntisymmetric :
  forall {A : Type} (R : rel A),
    Symmetric R -> Antisymmetric R -> R --> eq.
(* begin hide *)
Proof.
  intros A R [HS] [HAS] x y rxy.
  assert (ryx : R y x) by (apply HS; assumption).
  apply HAS in rxy. contradiction.
Qed.
(* end hide *)

Lemma Reflexive_Symmetric_WeaklyAntisymmetric_spec :
  forall {A : Type} (R : rel A),
    Reflexive R -> Symmetric R -> Antisymmetric R -> R <--> eq.
(* begin hide *)
Proof.
  intros A R HR HS HAS; split.
  - apply eq_greatest_Symmetric_WeaklyAntisymmetric; assumption.
  - apply eq_subrelation_Reflexive; assumption.
Qed.
(* end hide *)

Lemma Symmetric_Total_spec :
  forall {A : Type} (R : rel A),
    Symmetric R -> Total R -> R <--> RTrue.
(* begin hide *)
Proof.
  intros A R [HS] [HT]; split.
  - intros x y r. red. trivial.
  - intros x y _. destruct (HT x y); [| apply HS]; assumption.
Qed.
(* end hide *)

Lemma LeftEuclidean_spec :
  forall {A : Type} (R : rel A),
    LeftEuclidean R <-> forall x y z : A, R x y -> R x z -> R z y.
(* begin hide *)
Proof.
  unfold LeftEuclidean. firstorder.
Abort.
(* end hide *)

Search Symmetric WeaklyAntisymmetric.

(** ** Relacje słaboantysymetryczne względem pewnej relacji równoważności *)

Class WeaklyAntisymmetric' {A : Type} {E : rel A}
  (H : Equivalence E) (R : rel A) : Prop :=
{
    wasym : forall x y : A, R x y -> R y x -> E x y
}.

#[export]
Instance WeaklyAntisymmetric'_Equivalence :
  forall (A : Type) (E : rel A) (H : Equivalence E),
    WeaklyAntisymmetric' H E.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance WeaklyAntisymmetric'_Rinv :
  forall (A : Type) (E : rel A) (H : Equivalence E) (R : rel A),
    WeaklyAntisymmetric' H R -> WeaklyAntisymmetric' H (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_WeaklyAntisymmetric'_Rcomp :
  exists (A : Type) (E R S : rel A), forall H : Equivalence E,
    WeaklyAntisymmetric' H R /\ WeaklyAntisymmetric' H S /\
      ~ WeaklyAntisymmetric' H (Rcomp R S).
(* begin hide *)
Proof.
  pose (R := fun b b' : bool =>
    if orb (andb b (negb b')) (andb (negb b) (negb b')) then True else False).
  pose (S := fun b b' : bool =>
    if orb (andb (negb b) b') (andb (negb b) (negb b')) then True else False).
  exists bool, (@eq bool), R, S. intros. repeat split.
    destruct x, y; cbn; do 2 inversion 1; auto.
    destruct x, y; cbn; do 2 inversion 1; auto.
    unfold Rcomp; destruct 1. cut (true = false).
      inversion 1.
      apply wasym0.
        exists false. cbn. auto.
        exists false. cbn. auto.
Qed.
(* end hide *)

Lemma not_WeaklyAntisymmetric'_Rnot :
  exists (A : Type) (E R : rel A), forall H : Equivalence E,
    WeaklyAntisymmetric' H R /\ ~ WeaklyAntisymmetric' H (Rnot R).
(* begin hide *)
Proof.
  pose (R := fun b b' : bool => if andb b b' then True else False).
  exists bool, (@eq bool), R. intros. repeat split; intros.
    destruct x, y; compute in *; intuition.
    unfold Rnot; destruct 1.
      cut (true = false).
        inversion 1.
        apply wasym0; auto.
Qed.
(* end hide *)

Lemma not_WeaklyAntisymmetric'_Ror :
  exists (A : Type) (E R S : rel A), forall H : Equivalence E,
    WeaklyAntisymmetric' H R /\ WeaklyAntisymmetric' H S /\
      ~ WeaklyAntisymmetric' H (Ror R S).
(* begin hide *)
Proof.
  pose (R := fun b b' : bool =>
    if orb (andb b (negb b')) (andb (negb b) (negb b')) then True else False).
  pose (S := fun b b' : bool =>
    if orb (andb (negb b) b') (andb (negb b) (negb b')) then True else False).
  exists bool, (@eq bool), R, S. intros. repeat split.
    destruct x, y; cbn; do 2 inversion 1; auto.
    destruct x, y; cbn; do 2 inversion 1; auto.
    unfold Ror; destruct 1. cut (true = false).
      inversion 1.
      apply wasym0; cbn; auto.
Qed.
(* end hide *)

#[export]
Instance WeaklyAntisymmetric'_Rand :
  forall (A : Type) (E : rel A) (H : Equivalence E) (R S : rel A),
    WeaklyAntisymmetric' H R -> WeaklyAntisymmetric' H S ->
      WeaklyAntisymmetric' H (Rand R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** * Domknięcia (TODO) *)

Require Import Classes.RelationClasses.

(** ** Domknięcie zwrotne *)

Inductive rc {A : Type} (R : rel A) : rel A :=
| rc_step : forall x y : A, R x y -> rc R x y
| rc_refl : forall x : A, rc R x x.

(* begin hide *)
#[global] Hint Constructors rc : core.

Ltac rc := compute; repeat split; intros; rel;
repeat match goal with
| H : rc _ _ _ |- _ => induction H; eauto
end; rel.
(* end hide *)

#[export]
Instance Reflexive_rc :
  forall (A : Type) (R : rel A), Reflexive (rc R).
(* begin hide *)
Proof. rc. Qed.
(* end hide *)

Lemma subrelation_rc :
  forall (A : Type) (R : rel A), subrelation R (rc R).
(* begin hide *)
Proof. rc. Qed.
(* end hide *)

Lemma rc_smallest :
  forall (A : Type) (R S : rel A),
    subrelation R S -> Reflexive S -> subrelation (rc R) S.
(* begin hide *)
Proof. rc. Qed.
(* end hide *)

Lemma rc_idempotent :
  forall (A : Type) (R : rel A),
    rc (rc R) <--> rc R.
(* begin hide *)
Proof. rc. Qed.
(* end hide *)

Lemma rc_Rinv :
  forall (A : Type) (R : rel A),
    Rinv (rc (Rinv R)) <--> rc R.
(* begin hide *)
Proof. rc. Qed.
(* end hide *)

(** ** Domknięcie symetryczne *)

Inductive sc {A : Type} (R : rel A) : rel A :=
| sc_step : forall x y : A, R x y -> sc R x y
| sc_symm : forall x y : A, R x y -> sc R y x.

(* begin hide *)
#[global] Hint Constructors sc : core.

Ltac sc := compute; repeat split; intros; rel;
repeat match goal with
| H : sc _ _ _ |- _ => inversion H; eauto
end.
(* end hide *)

#[export]
Instance Symmetric_sc :
  forall (A : Type) (R : rel A), Symmetric (sc R).
(* begin hide *)
Proof. sc. Qed.
(* end hide *)

Lemma subrelation_sc :
  forall (A : Type) (R : rel A), subrelation R (sc R).
(* begin hide *)
Proof. sc. Qed.
(* end hide *)

Lemma sc_smallest :
  forall (A : Type) (R S : rel A),
    subrelation R S -> Symmetric S -> subrelation (sc R) S.
(* begin hide *)
Proof. sc. Qed.
(* end hide *)

Lemma sc_idempotent :
  forall (A : Type) (R : rel A),
    sc (sc R) <--> sc R.
(* begin hide *)
Proof. sc. Qed.
(* end hide *)

Lemma sc_Rinv :
  forall (A : Type) (R : rel A),
    Rinv (sc (Rinv R)) <--> sc R.
(* begin hide *)
Proof. sc. Qed.
(* end hide *)

(** **** Ćwiczenie (gorsze domknięcie symetryczne) *)

(** Przyjrzyj się poniższej alternatywnej definicji domknięcia symetrycznego.
    Udowodnij, że jest ona równoważna [sc]. Dlaczego jest ona gorsza niż [sc]? *)

Inductive sc' {A : Type} (R : rel A) : rel A :=
| sc'_step :
    forall x y : A, R x y -> sc' R x y
| sc'_symm :
    forall x y : A, sc' R x y -> sc' R y x.

(* begin hide *)
#[global] Hint Constructors sc' : core.

Ltac sc' := compute; repeat split; intros; rel;
repeat match goal with
| H : sc' _ _ _ |- _ => induction H; eauto
end.
(* end hide *)

#[export]
Instance Symmetric_sc' :
  forall (A : Type) (R : rel A), Symmetric (sc' R).
(* begin hide *)
Proof. sc'. Qed.
(* end hide *)

Lemma subrelation_sc' :
  forall (A : Type) (R : rel A), subrelation R (sc' R).
(* begin hide *)
Proof. sc'. Qed.
(* end hide *)

Lemma sc'_smallest :
  forall (A : Type) (R S : rel A),
    subrelation R S -> Symmetric S -> subrelation (sc' R) S.
(* begin hide *)
Proof. sc'. Qed.
(* end hide *)

Lemma sc'_idempotent :
  forall (A : Type) (R : rel A),
    sc' (sc' R) <--> sc' R.
(* begin hide *)
Proof. sc'. Qed.
(* end hide *)

Lemma sc'_Rinv :
  forall (A : Type) (R : rel A),
    Rinv (sc' (Rinv R)) <--> sc' R.
(* begin hide *)
Proof. sc'. Qed.
(* end hide *)

Lemma sc_sc' :
  forall {A : Type} (R : rel A),
    sc R <--> sc' R.
(* begin hide *)
Proof.
  split; [sc |].
  intros x y H. induction H.
  - auto.
  - destruct IHsc'; auto.
Qed.
(* end hide *)

(** ** Domknięcie przechodnie *)

Inductive tc {A : Type} (R : rel A) : rel A :=
| tc_step : forall x y : A, R x y -> tc R x y
| tc_trans : forall x y z : A, R x y -> tc R y z -> tc R x z.

(* begin hide *)
#[global] Hint Constructors tc : core.

Ltac tc := compute; repeat split; intros; rel;
match goal with
| H : tc _ _ _ |- _ => inversion H; eauto
end.
(* end hide *)

#[export]
Instance Transitive_tc :
  forall (A : Type) (R : rel A),
    Transitive (tc R).
(* begin hide *)
Proof.
  unfold Transitive.
  intros A R x y z Hxy; revert z.
  induction Hxy.
  - intros z Hyz. constructor 2 with y; assumption.
  - intros w Hzw. constructor 2 with y.
    + assumption.
    + apply IHHxy. assumption.
Defined.
(* end hide *)

Lemma subrelation_tc :
  forall (A : Type) (R : rel A), subrelation R (tc R).
(* begin hide *)
Proof. tc. Qed.
(* end hide *)

Lemma tc_smallest :
  forall (A : Type) (R S : rel A),
    subrelation R S -> Transitive S ->
      subrelation (tc R) S.
(* begin hide *)
Proof.
  unfold subrelation, Transitive.
  intros A R S HRS HT x y.
  induction 1; eauto.
Qed.
(* end hide *)

Lemma tc_idempotent :
  forall (A : Type) (R : rel A),
    tc (tc R) <--> tc R.
(* begin hide *)
Proof.
  split.
  - induction 1.
    + assumption.
    + eapply Transitive_tc; eassumption.
  - induction 1.
    + auto.
    + eapply Transitive_tc; eauto.
Qed.
(* end hide *)

Lemma tc_Rinv :
  forall (A : Type) (R : rel A),
    Rinv (tc (Rinv R)) <--> tc R.
(* begin hide *)
Proof.
  unfold Rinv; intros A R; split.
  - intros x y H. induction H.
    + auto.
    + eapply Transitive_tc; eauto.
  - induction 1.
    + auto.
    + eapply Transitive_tc; eauto.
Qed.
(* end hide *)

(** **** Ćwiczenie (alternatywne domknięcie przechodnie) *)

(** Przyjrzyj się poniższej definicji domknięcia przechodniego. Udowodnij,
    że jest ona równoważna oryginalnej definicji. Czy poniższa definicja
    jest lepsza czy gorsza od oryginalnej? *)

Inductive tc' {A : Type} (R : rel A) : rel A :=
| tc'_step :
    forall x y : A, R x y -> tc' R x y
| tc'_trans :
    forall x y z : A,
      tc' R x y -> tc' R y z -> tc' R x z.

(* begin hide *)
#[global] Hint Constructors tc' : core.

Ltac tc' := compute; repeat split; intros; rel;
repeat match goal with
| H : tc' _ _ _ |- _ => induction H; eauto
end.

#[export]
Instance Transitive_tc' :
  forall (A : Type) (R : rel A), Transitive (tc' R).
Proof. tc'. Qed.
(* end hide *)

Lemma tc_tc' :
  forall (A : Type) (R : rel A),
    tc R <--> tc' R.
(* begin hide *)
Proof.
  split.
  - induction 1; eauto.
  - induction 1.
    + auto.
    + eapply Transitive_tc; eassumption.
Qed.
(* end hide *)

(** ** Domknięcie zwrotnosymetryczne *)

Definition rsc {A : Type} (R : rel A) : rel A :=
  rc (sc' R).

(* begin hide *)
Ltac rstc := compute; repeat split; intros; rel;
repeat match goal with
| H : rc _ _ _ |- _ => induction H; eauto
| H : sc' _ _ _ |- _ => induction H; eauto
| H : tc' _ _ _ |- _ => induction H; eauto
end; rel.
(* end hide *)

#[export]
Instance Reflexive_rsc :
  forall (A : Type) (R : rel A), Reflexive (rsc R).
(* begin hide *)
Proof. rstc. Qed.
(* end hide *)

#[export]
Instance Symmetric_rsc :
  forall (A : Type) (R : rel A), Symmetric (rsc R).
(* begin hide *)
Proof. rstc. Qed.
(* end hide *)

Lemma subrelation_rsc :
  forall (A : Type) (R : rel A), subrelation R (rsc R).
(* begin hide *)
Proof. rstc. Qed.
(* end hide *)

Lemma rsc_smallest :
  forall (A : Type) (R S : rel A),
    subrelation R S -> Reflexive S -> Symmetric S ->
      subrelation (rsc R) S.
(* begin hide *)
Proof. rstc. Qed.
(* end hide *)

Lemma rsc_idempotent :
  forall (A : Type) (R : rel A),
    rsc (rsc R) <--> rsc R.
(* begin hide *)
Proof. rstc. Qed.
(* end hide *)

Lemma rsc_Rinv :
  forall (A : Type) (R : rel A),
    Rinv (rsc (Rinv R)) <--> rsc R.
(* begin hide *)
Proof. rstc. Qed.
(* end hide *)

(** ** Domknięcie zwrotnoprzechodnie *)

Inductive rtc {A : Type} (R : rel A) : rel A :=
(* | rtc_step  : forall x y : A, R x y ->  *)
| rtc_refl  : forall x : A, rtc R x x
| rtc_trans : forall x y z : A, R x y -> rtc R y z -> rtc R x z.

Lemma rtc_step :
  forall {A : Type} (R : rel A) (x y : A),
    R x y -> rtc R x y.
(* begin hide *)
Proof.
  intros A R x y. right with y.
  - assumption.
  - constructor.
Qed.
(* end hide *)

#[export]
Instance Reflexive_rtc :
  forall {A : Type} (R : rel A),
    Reflexive (rtc R).
(* begin hide *)
Proof.
  intros A R x. constructor.
Qed.
(* end hide *)

#[export]
Instance Transitive_rtc :
  forall {A : Type} (R : rel A),
    Transitive (rtc R).
(* begin hide *)
Proof.
  intros A R x y z rxy ryz; revert z ryz.
  induction rxy.
  - intros. assumption.
  - intros w rzw.
    right with y; [assumption |].
    apply IHrxy. assumption.
Qed.
(* end hide *)

Lemma rtc_RTrue_spec :
  forall A : Type, rtc (@RTrue A A) <--> RTrue.
(* begin hide *)
Proof.
  split; compute.
  - trivial.
  - intros x y _. apply rtc_step. trivial.
Qed.
(* end hide *)

(** Ćwiczneie (alternatywna definicja) *)

(** Pokaż, że poniższa alternatywna definicja domknięcia zwrotno-przechodniego
    jest równoważna oryginalnej. Która jest lepsza? *)

Definition rtc' {A : Type} (R : rel A) : rel A :=
  rc (tc R).

Lemma rtc_rtc' :
  forall {A : Type} (R : rel A),
    rtc R <--> rtc' R.
(* begin hide *)
Proof.
  split.
  - induction 1.
    + reflexivity.
    +
Admitted.
(* end hide *)

(** ** Domknięcie równoważnościowe *)

Definition ec {A : Type} (R : rel A) : rel A :=
  rtc (sc R).

(* begin hide *)
Ltac ec := compute; repeat split; intros; rel;
repeat match goal with
| H : ec _ _ _ |- _ => induction H; eauto
end.
(* end hide *)

#[export]
Instance Reflexive_ec :
  forall {A : Type} (R : rel A),
    Reflexive (ec R).
(* begin hide *)
Proof.
  typeclasses eauto.
Qed.
(* end hide *)

#[export]
Instance Symmetric_ec :
  forall {A : Type} (R : rel A),
    Symmetric (ec R).
(* begin hide *)
Proof.
  unfold ec, Symmetric.
  intros A R x y. induction 1.
  - constructor.
  - transitivity y.
    + auto.
    + eapply rtc_trans.
      * symmetry. eassumption.
      * reflexivity.
Qed.
(* end hide *)

#[export]
Instance Transitive_ec :
  forall {A : Type} (R : rel A),
    Transitive (ec R).
(* begin hide *)
Proof.
  typeclasses eauto.
Qed.
(* end hide *)

#[export]
Instance Equivalence_ec :
  forall (A : Type) (R : rel A), Equivalence (ec R).
(* begin hide *)
Proof.
  split; typeclasses eauto.
Qed.
(* end hide *)

Lemma subrelation_ec :
  forall (A : Type) (R : rel A), subrelation R (ec R).
(* begin hide *)
Proof.
  intros A R x y r. apply rtc_step. auto.
Qed.
(* end hide *)

Lemma ec_smallest :
  forall (A : Type) (R S : rel A),
    subrelation R S -> Equivalence S ->
      subrelation (ec R) S.
(* begin hide *)
Proof.
  unfold subrelation.
  intros A R S HRS [HR HS HT] x y e.
  induction e.
  - apply HR.
  - inversion H; subst; eauto.
Qed.
(* end hide *)

Lemma ec_idempotent :
  forall (A : Type) (R : rel A),
    ec (ec R) <--> ec R.
(* begin hide *)
Proof.

Admitted.
(* end hide *)

Lemma ec_Rinv :
  forall (A : Type) (R : rel A),
    Rinv (ec (Rinv R)) <--> ec R.
(* begin hide *)
Proof.

Admitted.
(* end hide *)

(** **** Ćwiczenie (alternatywne definicje) *)

(** Pokaż, że poniższe alternatywne definicje domknięcia równoważnościowego
    są równoważne oryginalnej. Która definicja jest najlepsza? *)

Inductive equiv_clos {A : Type} (R : rel A) : rel A :=
| equiv_clos_step :
    forall x y : A, R x y -> equiv_clos R x y
| equiv_clos_refl :
    forall x : A, equiv_clos R x x
| equiv_clos_symm :
    forall x y : A, equiv_clos R x y -> equiv_clos R y x
| equiv_clos_trans :
    forall x y z : A,
      equiv_clos R x y -> equiv_clos R y z -> equiv_clos R x z.

(* begin hide *)
#[global] Hint Constructors equiv_clos : core.

Ltac ec' := compute; repeat split; intros; rel;
repeat match goal with
| H : equiv_clos _ _ _ |- _ => induction H; eauto
end.
(* end hide *)

#[export]
Instance Equivalence_equiv_clos :
  forall (A : Type) (R : rel A), Equivalence (equiv_clos R).
(* begin hide *)
Proof. ec'. Qed.
(* end hide *)

Lemma ec_equiv_clos :
  forall {A : Type} (R : rel A),
    ec R <--> equiv_clos R.
(* begin hide *)
Proof.
  unfold ec.
  split.
  - induction 1; [auto |].
    transitivity y; [| auto].
    inversion H; auto.
  - induction 1.
    + eapply rtc_trans; [eauto |]. apply rtc_refl.
    + apply rtc_refl.
    + symmetry. assumption.
    + transitivity y; assumption.
Qed.
(* end hide *)

Definition rstc {A : Type} (R : rel A) : rel A :=
  tc' (sc' (rc R)).

#[export]
Instance Reflexive_rstc :
  forall {A : Type} (R : rel A),
    Reflexive (rstc R).
(* begin hide *)
Proof. rstc. Qed.
(* end hide *)

#[export]
Instance Symmetric_rstc :
  forall {A : Type} (R : rel A),
    Symmetric (rstc R).
(* begin hide *)
Proof. rstc. Qed.
(* end hide *)

#[export]
Instance Transitive_rstc :
  forall {A : Type} (R : rel A),
    Transitive (rstc R).
(* begin hide *)
Proof. rstc. Qed.
(* end hide *)

#[export]
Instance Equivalence_rstc :
  forall (A : Type) (R : rel A),
    Equivalence (rstc R).
(* begin hide *)
Proof. rstc. Qed.
(* end hide *)

Lemma rstc_equiv_clos :
  forall {A : Type} (R : rel A),
    rstc R <--> equiv_clos R.
(* begin hide *)
Proof.
  split.
    induction 1.
      induction H.
        destruct H; auto.
        auto.
      eauto.
    induction 1; auto.
      do 3 constructor. assumption.
      reflexivity.
      symmetry. assumption.
      rewrite IHequiv_clos1. assumption.
Qed.
(* end hide *)

Inductive EquivalenceClosure {A : Type} (R : rel A) : rel A :=
| EC_step  : forall x y   : A, R x y -> EquivalenceClosure R x y
| EC_refl  : forall x     : A,          EquivalenceClosure R x x
| EC_symm  : forall x y   : A, R x y -> EquivalenceClosure R y x
| EC_trans : forall x y z : A, R x y -> EquivalenceClosure R y z -> EquivalenceClosure R x z.

#[global] Hint Constructors EquivalenceClosure : core.

#[export]
Instance Reflexive_EquivalenceClosure :
  forall {A : Type} (R : rel A),
    Reflexive (EquivalenceClosure R).
(* begin hide *)
Proof.
  intros A R x. auto.
Qed.
(* end hide *)

#[export]
Instance Symmetric_EquivalenceClosure :
  forall {A : Type} (R : rel A),
    Symmetric (EquivalenceClosure R).
(* begin hide *)
Proof.
  intros A R x y H.
  induction H.
  - constructor 3. assumption.
  - constructor 2.
  - constructor 1. assumption.
Abort.
(* end hide *)

#[export]
Instance Transitive_EquivalenceClosure :
  forall {A : Type} (R : rel A),
    Transitive (EquivalenceClosure R).
(* begin hide *)
Proof.
  intros A R x y z Hxy Hyz; revert z Hyz.
  induction Hxy; intros.
  - eauto.
  - auto.
  - constructor 1.
Abort.
(* end hide *)

Lemma EquivalenceClosure_equiv_clos :
  forall {A : Type} (R : rel A),
    EquivalenceClosure R <--> equiv_clos R.
(* begin hide *)
Proof.
  split.
  - intros x y H. induction H; eauto.
  - intros x y H. induction H.
    1-2: auto.
Abort.
(* end hide *)

Definition EquivalenceClosure' {A : Type} (R : rel A) : rel A :=
  rc (tc' (sc' R)).

#[export]
Instance Reflexive_EquivalenceClosure' :
  forall {A : Type} (R : rel A),
    Reflexive (EquivalenceClosure' R).
(* begin hide *)
Proof.
  typeclasses eauto.
Qed.
(* end hide *)

#[export]
Instance Symmetric_EquivalenceClosure' :
  forall {A : Type} (R : rel A),
    Symmetric (EquivalenceClosure' R).
(* begin hide *)
Proof.
  unfold EquivalenceClosure', Symmetric.
  destruct 1; [| auto].
  constructor.
  induction H.
  - constructor. symmetry. assumption.
  - transitivity y; assumption.
Qed.
(* end hide *)

#[export]
Instance Transitive_EquivalenceClosure' :
  forall {A : Type} (R : rel A),
    Transitive (EquivalenceClosure' R).
(* begin hide *)
Proof.
  unfold EquivalenceClosure', Transitive.
  intros A R x y z Hxy Hyz.
  inversion Hxy as [? ? Hxy' |]; subst; clear Hxy; [| auto].
  inversion Hyz as [? ? Hyz' |]; subst; clear Hyz; [| auto].
  constructor. transitivity y; assumption.
Qed.
(* end hide *)

Lemma EquivalenceClosure'_equiv_clos :
  forall {A : Type} (R : rel A),
    EquivalenceClosure' R <--> equiv_clos R.
(* begin hide *)
Proof.
  unfold EquivalenceClosure'.
  split.
  - inversion_clear 1 as [? ? Ht |]; [| auto].
    induction Ht.
    + induction H; auto.
    + transitivity y; assumption.
  - induction 1; [auto | auto | | ].
    + symmetry. assumption.
    + transitivity y; assumption.
Qed.
(* end hide *)

(** ** Domknięcie cyrkularne *)

Inductive CircularClosure {A : Type} (R : rel A) : rel A :=
| CC_step  :
    forall x y : A, R x y -> CircularClosure R x y
| CC_circ :
    forall x y z : A,
      CircularClosure R x y -> CircularClosure R y z ->
        CircularClosure R z x.

#[export]
Instance Circular_CircularClosure
  {A : Type} (R : rel A) : Circular (CircularClosure R).
(* begin hide *)
Proof.
  split; intros x y z H1 H2; revert z H2.
  induction H1.
  - destruct 1.
    + eright; constructor; eassumption.
    + eright with z.
      * constructor; assumption.
      * eright; eassumption.
  - intros. eright with x.
    + eright with y; eassumption.
    + assumption.
Qed.
(* end hide *)

(** ** Domknięcie lewostronnie kwazizwrotne *)

Inductive LeftQuasiReflexiveClosure {A : Type} (R : rel A) : rel A :=
| LQRC_step :
    forall x y : A, R x y -> LeftQuasiReflexiveClosure R x y
| LQRC_clos :
    forall x y : A, R x y -> LeftQuasiReflexiveClosure R x x.

#[export]
Instance LeftQuasiReflexive_LeftQuasiReflexiveClosure
  {A : Type} (R : rel A) : LeftQuasiReflexive (LeftQuasiReflexiveClosure R).
(* begin hide *)
Proof.
  unfold LeftQuasiReflexive.
  intros x y [r | r].
  - right with y0. assumption.
  - right with y0. assumption.
Qed.
(* end hide *)

(** ** Domknięcie słabozwrotne (TODO) *)

Module CoReflexiveClosure.

Private Inductive CoReflexiveClosureCarrier {A : Type} (R : rel A) : Type :=
| embed  : A -> CoReflexiveClosureCarrier R.

Arguments embed {A R} _.

Axiom WRCC_equal :
  forall {A : Type} {x y : A} {R : rel A},
    R x y -> @embed _ R x = @embed _ R y.

Inductive CoReflexiveClosure {A : Type} (R : rel A)
  : rel (CoReflexiveClosureCarrier R) :=
| step : forall x y : A, R x y -> CoReflexiveClosure R (embed x) (embed y).

End CoReflexiveClosure.

(** ** Ogólne pojęcie domknięcia *)

(** Uwaga, najnowszy pomysł: przedstawić domknięcia w taki sposób, żeby
    niepostrzeżenie przywyczajały do monad. *)

Class Closure
  {A : Type}
  (Cl : rel A -> rel A) : Prop :=
{
    pres :
      forall R S : rel A,
        (forall x y : A, R x y -> S x y) ->
          forall x y : A, Cl R x y -> Cl S x y;
    step :
      forall R : rel A,
        forall x y : A, R x y -> Cl R x y;
    join :
      forall R : rel A,
        forall x y : A, Cl (Cl R) x y -> Cl R x y;
}.

#[refine]
#[export]
Instance Closure_rc {A : Type} : Closure (@rc A) :=
{
    step := rc_step;
}.
(* begin hide *)
Proof.
  induction 2.
    constructor. apply H. assumption.
    constructor 2.
  inversion 1; subst.
    assumption.
    constructor 2.
Qed.
(* end hide *)

(** * Redukcje (TODO) *)

(** ** Redukacja zwrotna *)

Definition rr {A : Type} (R : rel A) : rel A :=
  fun x y : A => R x y /\ x <> y.

#[export]
Instance Antireflexive_rr :
  forall (A : Type) (R : rel A), Antireflexive (rr R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

From Typonomikon Require Import B4.

Lemma rr_rc :
  LEM ->
    forall (A : Type) (R : rel A),
      Reflexive R -> rc (rr R) <--> R.
(* begin hide *)
Proof.
  intro lem. rc.
  destruct (lem (a = b)).
    subst. constructor 2.
    constructor. split; auto.
Qed.
(* end hide *)

(** ** Redukcja przechodnia *)

Definition TransitiveReduction {A : Type} (R : rel A) (x y : A) : Prop :=
  R x y /\ forall z : A, R x z -> R z y -> False.

#[export]
Instance Antitransitive_TransitiveReduction
  {A : Type} (R : rel A)
  : Antitransitive (TransitiveReduction R).
(* begin hide *)
Proof.
  compute. intros x y z [H11 H12] [H21 H22] [H31 H32].
  firstorder.
Qed.
(* end hide *)

Definition TransitiveReduction' {A : Type} (R : rel A) (x y : A) : Prop :=
  R x y /\ forall z : A, rr R x z -> rr R z y -> False.

#[export]
Instance Antitransitive_TransitiveReduction'
  {A : Type} (R : rel A)
  : Antitransitive (TransitiveReduction' R).
(* begin hide *)
Proof.
  compute. intros x y z [H11 H12] [H21 H22] [H31 H32].
Abort.
(* end hide *)

(** * Cosik o systemach przepisywania *)

(** ** Właściwość diamentu *)

Class Diamond {A : Type} (R : rel A) : Prop :=
{
    diamond :
      forall x y z : A,
        R x y -> R x z ->
          exists w : A, R y w /\ R z w
}.

#[export]
Instance Diamond_RTrue :
  forall A : Type, Diamond (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Diamond_RFalse :
  forall A : Type, Diamond (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Diamond_eq :
  forall A : Type, Diamond (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Diamond_lt :
  Diamond lt.
(* begin hide *)
Proof.
  split; intros. exists (1 + y + z). lia.
Qed.
(* end hide *)

#[export]
Instance Diamond_le :
  Diamond le.
(* begin hide *)
Proof.
  split; intros. exists (1 + y + z). lia.
Qed.
(* end hide *)

Lemma not_Diamond_gt :
  ~ Diamond gt.
(* begin hide *)
Proof.
  intros [HC].
  destruct (HC 1 0 0 ltac:(lia) ltac:(lia)).
  lia.
Qed.
(* end hide *)

#[export]
Instance Diamond_ge :
  Diamond ge.
(* begin hide *)
Proof.
  split; intros. exists 0. lia.
Qed.
(* end hide *)

Lemma not_Diamond_Rinv :
  exists (A : Type) (R : rel A),
    Diamond R /\ ~ Diamond (Rinv R).
(* begin hide *)
Proof.
  exists nat, lt.
  split; [split |].
  - intros x y z Hxy Hxz. exists (1 + y + z). lia.
  - unfold Rinv; intros [HC].
    destruct (HC 2 0 0 ltac:(lia) ltac:(lia)) as (w & H1 & _).
    lia.
Qed.
(* end hide *)

Lemma not_Diamond_Rcomp :
  exists (A : Type) (R S : rel A),
    Diamond R /\ Diamond S /\ ~ Diamond (Rcomp R S).
(* begin hide *)
Proof.
Abort.
(* end hide *)

Lemma not_Diamond_Rnot :
  exists (A : Type) (R : rel A),
    Diamond R /\ ~ Diamond (Rnot R).
(* begin hide *)
Proof.
  exists nat, le.
  split; [split |].
  - apply Diamond_le.
  - unfold Rnot; intros [HC].
    destruct (HC 1 0 0 ltac:(lia) ltac:(lia)) as (w & H1 & H2).
    lia.
Qed.
(* end hide *)

Lemma not_Diamond_Ror :
  exists (A : Type) (R S : rel A),
    Diamond R /\ Diamond S /\ ~ Diamond (Ror R S).
(* begin hide *)
Proof.
  exists
    nat,
    (fun x y => y = 2 + x),
    (fun x y => y = 2 * x).
  split; [| split].
  - split. intros x y z -> ->. eauto.
  - split. intros x y z -> ->. eauto.
  - unfold Ror. intros [HC].
    destruct (HC 0 2 0) as (w & [Hw1 | Hw1] & [Hw2 | Hw2]); lia.
Qed.
(* end hide *)

Lemma not_Diamond_Rand :
  exists (A : Type) (R S : rel A),
    Diamond R /\ Diamond S /\ ~ Diamond (Rand R S).
(* begin hide *)
Proof.
  exists
    nat,
    (fun x y => y = 1 - x),
    (fun x y => y = 2 - x).
  split; [| split].
  - split. intros x y z -> ->. eauto.
  - split. intros x y z -> ->. eauto.
  - unfold Rand. intros [HC].
    destruct (HC 2 0 0) as [w [[Hw1 Hw2] [Hw3 Hw4]]]; lia.
Qed.
(* end hide *)

(** ** Relacje lokalnie konfluentne *)

Class LocallyConfluent {A : Type} (R : rel A) : Prop :=
  locally_confluent :
    forall x y z : A, R x y -> R x z -> exists w : A, rtc R y w /\ rtc R z w.

#[export]
Instance LocallyConfluent_RTrue :
  forall A : Type, LocallyConfluent (@RTrue A A).
(* begin hide *)
Proof.
  unfold LocallyConfluent.
  intros A x y z _ _.
  exists x. split; apply rtc_step; compute; trivial.
Qed.
(* end hide *)

#[export]
Instance LocallyConfluent_RFalse :
  forall A : Type, LocallyConfluent (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance LocallyConfluent_eq :
  forall A : Type, LocallyConfluent (@eq A).
(* begin hide *)
Proof.
  unfold LocallyConfluent.
  intros A x y z -> ->.
  exists z. split; apply rtc_refl.
Qed.
(* end hide *)

#[export]
Instance LocallyConfluent_Diamond :
  forall {A : Type} (R : rel A),
    Diamond R -> LocallyConfluent R.
(* begin hide *)
Proof.
  intros A R [HD] x y z rxy rxz.
  destruct (HD _ _ _ rxy rxz) as (w & ryw & rzw).
  exists w. split; apply rtc_step; assumption.
Qed.
(* end hide *)

Lemma not_LocallyConfluent_gt :
  ~ LocallyConfluent gt.
(* begin hide *)
Proof.
  unfold LocallyConfluent.
  intros HD.
  destruct (HD 1 0 0 ltac:(lia) ltac:(lia)) as (w & Hw1 & Hw2).
Abort.
(* end hide *)

Lemma not_LocallyConfluent_Rinv :
  exists (A : Type) (R : rel A),
    LocallyConfluent R /\ ~ LocallyConfluent (Rinv R).
(* begin hide *)
Proof.
  exists nat, lt.
  split.
  - apply LocallyConfluent_Diamond. typeclasses eauto.
  - unfold LocallyConfluent, Rinv. intros HD.
    specialize (HD 1 0 0 ltac:(lia) ltac:(lia)).
Abort.
(* end hide *)

Lemma not_LocallyConfluent_Rcomp :
  exists (A : Type) (R S : rel A),
    LocallyConfluent R /\ LocallyConfluent S /\ ~ LocallyConfluent (Rcomp R S).
(* begin hide *)
Proof.
Abort.
(* end hide *)

Lemma not_LocallyConfluent_Rnot :
  exists (A : Type) (R : rel A),
    LocallyConfluent R /\ ~ LocallyConfluent (Rnot R).
(* begin hide *)
Proof.
  exists nat, le.
Abort.
(* end hide *)

Lemma not_LocallyConfluent_Ror :
  exists (A : Type) (R S : rel A),
    LocallyConfluent R /\ LocallyConfluent S /\ ~ LocallyConfluent (Ror R S).
(* begin hide *)
Proof.
  exists
    nat,
    (fun x y => y = 2 + x),
    (fun x y => y = 2 * x).
  split; [| split].
  - intros x y z -> ->.
Abort.
(* end hide *)

Lemma not_LocallyConfluent_Rand :
  exists (A : Type) (R S : rel A),
    LocallyConfluent R /\ LocallyConfluent S /\ ~ LocallyConfluent (Rand R S).
(* begin hide *)
Proof.
  exists
    nat,
    (fun x y => y = 1 - x),
    (fun x y => y = 2 - x).
Abort.
(* end hide *)

(** ** Relacje konfluentne *)

Class Confluent {A : Type} (R : rel A) : Prop :=
  confluent :
    forall x y z : A, rtc R x y -> rtc R x z -> exists w : A, rtc R y w /\ rtc R z w.

#[export]
Instance Confluent_RTrue :
  forall A : Type, Confluent (@RTrue A A).
(* begin hide *)
Proof.
  unfold Confluent.
  intros A x y z _ _.
  exists x. split; apply rtc_step; compute; trivial.
Qed.
(* end hide *)

#[export]
Instance Confluent_RFalse :
  forall A : Type, Confluent (@RFalse A A).
(* begin hide *)
Proof.
  unfold Confluent.
  intros A x y z rrxy rrxz; revert z rrxz.
  induction rrxy.
  - intros z rrxz. exists z; split; [assumption | apply rtc_refl].
  - inversion H.
Qed.
(* end hide *)

#[export]
Instance Confluent_eq :
  forall A : Type, Confluent (@eq A).
(* begin hide *)
Proof.
  unfold Confluent.
  intros A x y z rrxy rrxz; revert z rrxz.
  induction rrxy.
  - intros z rrxz. exists z. split; [assumption | apply rtc_refl].
  - intros w rrxw. subst. destruct (IHrrxy _ rrxw) as (w' & rrzw' & rrzw'').
    exists w'. split; assumption.
Qed.
(* end hide *)

Lemma not_Confluent_Rinv :
  exists (A : Type) (R : rel A),
    Confluent R /\ ~ Confluent (Rinv R).
(* begin hide *)
Proof.
  exists nat, lt.
Abort.
(* end hide *)

Lemma not_Confluent_Rcomp :
  exists (A : Type) (R S : rel A),
    Confluent R /\ Confluent S /\ ~ Confluent (Rcomp R S).
(* begin hide *)
Proof.
Abort.
(* end hide *)

Lemma not_Confluent_Rnot :
  exists (A : Type) (R : rel A),
    Confluent R /\ ~ Confluent (Rnot R).
(* begin hide *)
Proof.
Abort.
(* end hide *)

Lemma not_Confluent_Ror :
  exists (A : Type) (R S : rel A),
    Confluent R /\ Confluent S /\ ~ Confluent (Ror R S).
(* begin hide *)
Proof.
Abort.
(* end hide *)

#[export]
Instance Confluent_Rand :
  forall {A : Type} (R S : rel A),
    Confluent R -> Confluent S -> Confluent (Rand R S).
(* begin hide *)
Proof.
  unfold Confluent.
  intros A R S HCR HCS x y z rs1 rs2; revert z rs2.
  induction rs1.
  - intros z rs. exists z. split; [assumption | apply rtc_refl].
  - intros w rs3. destruct H as [r s].
Abort.
(* end hide *)

Lemma not_Confluent_Rand :
  exists (A : Type) (R S : rel A),
    Confluent R /\ Confluent S /\ ~ Confluent (Rand R S).
(* begin hide *)
Proof.
  exists
    nat,
    (fun x y => y = 1 - x),
    (fun x y => y = 2 - x).
Abort.
(* end hide *)

(** * Podsumowanie *)

(** Do obczajenia z biblioteki stdpp: *)

(* Module wut.

From stdpp Require Import prelude.

Print strict.
Print diamond.
Print locally_confluent.
Print confluent.
Print Trichotomy.
Print PartialOrder.
Print Total.
Print TotalOrder.
Print relation_equivalence.
Print Setoid_Theory.
Print TrichotomyT.
Print DefaultRelation.
Print order.
Print antisymmetric.
Print RewriteRelation.
Print StrictOrder.
Print all_loop.
Print strict.
Print nf.
Print red.

End wut. *)