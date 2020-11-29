(** * H3: Relacje *)

(* begin hide *)

(* end hide *)

Require Import H2.
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
Hint Constructors le'.

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

Lemma Rid_left :
  forall (A B : Type) (R : hrel A B),
    Rcomp (@Rid A) R <--> R.
(* begin hide *)
Proof.
  compute; split; intros.
    decompose [ex and] H; subst; eauto.
    exists a; eauto.
Qed.
(* end hide *)

Lemma Rid_right :
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

Lemma Rinv_Rid :
  forall A : Type, same_hrel (@Rid A) (Rinv (@Rid A)).
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
    | H : False |- _ => inversion H
    | x : Empty_set |- _ => destruct x
    | H : True |- _ => inversion H
    | x : unit |- _ => destruct x
end; try congruence.
(* end hide *)

Lemma Rnot_double :
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
    relacje prawostronnie unikalne. *)

Instance LeftUnique_eq (A : Type) : LeftUnique (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

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

Instance LeftUnique_Rcomp :
  forall (A B C : Type) (R : hrel A B) (S : hrel B C),
    LeftUnique R -> LeftUnique S -> LeftUnique (Rcomp R S).
(* begin hide *)
Proof.
  rel. specialize (left_unique0 _ _ _ H0 H2). subst.
  apply left_unique1 with x0; assumption.
Qed.
(* end hide *)

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

Instance LeftUnique_Rinv :
  forall (A B : Type) (R : hrel A B),
    RightUnique R -> LeftUnique (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

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

Instance LeftUnique_Rand :
  forall (A B : Type) (R S : hrel A B),
    LeftUnique R -> LeftUnique (Rand R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Instance RightUnique_Rand :
  forall (A B : Type) (R S : hrel A B),
    RightUnique R -> RightUnique (Rand R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma Ror_not_LeftUnique :
  exists (A B : Type) (R S : hrel A B),
    LeftUnique R /\ LeftUnique S /\ ~ LeftUnique (Ror R S).
(* begin hide *)
Proof.
  exists bool, bool.
  exists (@Rid bool), (fun b b' => b = negb b').
  rel. cut (true = false).
    inversion 1.
    apply left_unique0 with false; auto.
Qed.
(* end hide *)

Lemma Ror_not_RightUnique :
  exists (A B : Type) (R S : hrel A B),
    RightUnique R /\ RightUnique S /\ ~ RightUnique (Ror R S).
(* begin hide *)
Proof.
  exists bool, bool.
  exists (@Rid bool), (fun b b' => b = negb b').
  rel.
    destruct b, b'; cbn in H0; congruence.
    cut (true = false).
      inversion 1.
      apply right_unique0 with false; auto.
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

Lemma Rnot_not_LeftUnique :
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

Lemma Rnot_not_RightUnique :
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

Lemma RTrue_bool_not_LeftUnique :
  ~ LeftUnique (@RTrue bool bool).
Proof.
  compute. destruct 1. cut (true = false).
    inversion 1.
    rel.
Qed.

Lemma RTrue_bool_not_RightUnique :
  ~ RightUnique (@RTrue bool bool).
Proof.
  compute. destruct 1. cut (true = false).
    inversion 1.
    rel.
Qed.

Definition is_zero (b : bool) (n : nat) : Prop :=
match n with
    | 0 => b = true
    | _ => b = false
end.

Instance LeftUnique_is_zero : LeftUnique is_zero.
Proof.
  split. intros. destruct b; cbn in *; subst; trivial.
Qed.

Lemma is_zero_not_RightUnique : ~ RightUnique is_zero.
Proof.
  destruct 1. cut (1 = 2).
    inversion 1.
    apply right_unique0 with false; cbn; trivial.
Qed.

Definition is_zero' : nat -> bool -> Prop := Rinv is_zero.

Lemma is_zero'_not_LeftUnique : ~ LeftUnique is_zero'.
Proof.
  destruct 1. cut (1 = 2).
    inversion 1.
    apply left_unique0 with false; cbn; trivial.
Qed.

Instance RightUnique_is_zero' : RightUnique is_zero'.
Proof.
  split. destruct a; cbn; intros; subst; trivial.
Qed.

Instance LeftUnique_RFalse :
  forall A B : Type, LeftUnique (@RFalse A B).
Proof. rel. Qed.

Instance RightUnique_RFalse :
  forall A B : Type, RightUnique (@RFalse A B).
Proof. rel. Qed.
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

    Za pojęciem tym nie stoją jakieś wielkie intuicje: relacja lewostronnie
    totalna to po prostu taka, w której żaden element [a : A] nie jest
    "osamotniony". *)

Instance LeftTotal_eq :
  forall A : Type, LeftTotal (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Instance RightTotal_eq :
  forall A : Type, RightTotal (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Równość jest relacją totalną, gdyż każdy term [x : A] jest równy samemu
    sobie. *)

Instance LeftTotal_Rcomp :
  forall (A B C : Type) (R : hrel A B) (S : hrel B C),
    LeftTotal R -> LeftTotal S -> LeftTotal (Rcomp R S).
(* begin hide *)
Proof.
  rel.
  destruct (left_total1 a) as [b H].
  destruct (left_total0 b) as [c H'].
  exists c, b. split; assumption.
Qed.
(* end hide *)

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

Instance RightTotal_Rinv :
  forall (A B : Type) (R : hrel A B),
    LeftTotal R -> RightTotal (Rinv R).
(* begin hide *)
Proof.
  unfold Rinv; split. intro a. destruct H.
  destruct (left_total0 a) as [b H]. exists b. assumption.
Qed.
(* end hide *)

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

Lemma Rand_not_LeftTotal :
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

Lemma Rand_not_RightTotal :
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

Lemma Rnot_not_LeftTotal :
  exists (A B : Type) (R : hrel A B),
    RightTotal R /\ ~ RightTotal (Rnot R).
(* begin hide *)
Proof.
  exists unit, unit, (@eq unit). rel.
  destruct (right_total0 tt), x. apply H. trivial.
Qed.
(* end hide *)

Lemma Rnot_not_RightTotal :
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

(** **** Ćwiczenie *)

(** Znajdź przykład relacji, która:
    - nie jest totalna ani lewostronnie, ani prawostronnie
    - jest totalna lewostronnie, ale nie prawostronnie
    - jest totalna prawostronnie, ale nie nie lewostronnie
    - jest obustronnie totalna *)

(** Bonusowe punkty za relację, która jest "naturalna", tzn. nie została
    wymyślona na chama specjalnie na potrzeby zadania. *)

(* begin hide *)
Lemma RFalse_nonempty_not_LeftTotal :
  forall A B : Type, A -> ~ LeftTotal (@RFalse A B).
Proof. rel. Qed.

Lemma RFalse_nonempty_not_RightTotal :
  forall A B : Type, B -> ~ RightTotal (@RFalse A B).
Proof. rel. Qed.

Instance LeftTotal_lt : LeftTotal lt.
Proof.
  split. intro. exists (S a). unfold lt. apply le_n.
Qed.

Lemma lt_not_RightTotal : ~ RightTotal lt.
Proof.
  destruct 1. destruct (right_total0 0). inversion H.
Qed.

Lemma gt_not_LeftTotal : ~ LeftTotal gt.
Proof.
  destruct 1. destruct (left_total0 0). inversion H.
Qed.

Instance RightTotal_gt : RightTotal gt.
Proof.
  split. intro. exists (S b). unfold gt, lt. trivial.
Qed.

Instance LeftTotal_nonempty_RTrue :
  forall A B : Type, B -> LeftTotal (@RTrue A B).
Proof. rel. Qed.

Instance RightTotal_nonempty_RTrue :
  forall A B : Type, A -> RightTotal (@RTrue A B).
Proof. rel. Qed.
(* end hide *)

(** * Rodzaje relacji heterogenicznych v2 *)

(** Poznawszy cztery właściwości, jakie relacje mogą posiadać, rozważymy
    teraz relacje, które posiadają dwie lub więcej z tych właściwości. *)

Class Functional {A B : Type} (R : hrel A B) : Prop :=
{
    F_LT :> LeftTotal R;
    F_RU :> RightUnique R;
}.

(** Lewostronną totalność i prawostronną unikalność możemy połączyć, by
    uzyskać pojęcie relacji funkcyjnej. Relacja funkcyjna to relacja,
    która ma właściwości takie, jak funkcje — każdy lewostronny argument
    [a : A] jest w relacji z dokładnie jednym [b : B] po prawej stronie. *)

Instance fun_to_Functional {A B : Type} (f : A -> B)
  : Functional (fun (a : A) (b : B) => f a = b).
(* begin hide *)
Proof.
  repeat split; intros.
    exists (f a). trivial.
    subst. trivial.
Qed.
(* end hide *)

(* begin hide *)
Definition Functional_to_fun
  {A B : Type} (R : hrel A B) (F : Functional R) : A -> B.
Proof.
  intro a. destruct F. destruct F_LT0.
  specialize (left_total0 a).
  Require Import IndefiniteDescription.
  apply constructive_indefinite_description in left_total0.
  destruct left_total0. exact x.
Qed.
(* end hide *)

(** Z każdej funkcji można w prosty sposób zrobić relację funkcyjną, ale
    bez dodatkowych aksjomatów nie jesteśmy w stanie z relacji funkcyjnej
    zrobić funkcji. Przemilczając kwestie aksjomatów możemy powiedzieć
    więc, że relacje funkcyjne odpowiadają funkcjom. *)

Instance Functional_eq :
  forall A : Type, Functional (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Równość jest rzecz jasna relacją funkcyjną. Funkcją odpowiadającą
    relacji [@eq A] jest funkcja identycznościowa [@id A]. *)

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

Lemma Rinv_not_Functional :
  exists (A B : Type) (R : hrel A B),
    Functional R /\ ~ Functional (Rinv R).
(* begin hide *)
Proof.
  exists bool, bool, (fun b b' => b' = true). split.
    rel.
    destruct 1. destruct F_LT0. destruct (left_total0 false) as [b H].
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

Lemma Rand_not_Functional :
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

Lemma Ror_not_Functional :
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

Lemma Rnot_not_Functional :
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
    pierwsze mają problem z [Rand], a drugie z [Ror], oba zaś z [Rnot. *)

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
    | c_trans : forall a b c : nat,
        collatz a b -> collatz b c -> collatz a c.

Hint Constructors collatz.

Lemma collatz_42 : collatz 42 1.
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
(* end hide *)

Class Injective {A B : Type} (R : hrel A B) : Prop :=
{
    I_Fun :> Functional R;
    I_LU :> LeftUnique R;
}.

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

Instance Injective_eq :
  forall A : Type, Injective (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

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

Lemma Rinv_not_Injective :
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

Lemma Rand_not_Injective :
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

Lemma Ror_not_Injective :
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

Lemma Rnot_not_Injective :
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

Class Surjective {A B : Type} (R : hrel A B) : Prop :=
{
    S_Fun :> Functional R;
    S_RT :> RightTotal R;
}.

Instance sur_to_Surjective :
  forall (A B : Type) (f : A -> B),
    surjective f -> Surjective (fun (a : A) (b : B) => f a = b).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Relacje funkcyjne, które są prawostronnie totalne, odpowiadają funkcjom
    surjektywnym. *)

Instance Surjective_eq :
  forall A : Type, Surjective (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

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

Lemma Rinv_not_Surjective :
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

Lemma Rand_not_Surjective :
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

Lemma Ror_not_Surjective :
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

Lemma Rnot_not_Surjective :
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

Class Bijective {A B : Type} (R : hrel A B) : Prop :=
{
    B_Fun :> Functional R;
    B_LU :> LeftUnique R;
    B_RT :> RightTotal R;
}.

Instance bij_to_Bijective :
  forall (A B : Type) (f : A -> B),
    bijective f -> Bijective (fun (a : A) (b : B) => f a = b).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Relacje funkcyjne, które są lewostronnie totalne (czyli injektywne) oraz
    prawostronnie totalne (czyli surjektywne), odpowiadają bijekcjom. *)

Instance Bijective_eq :
  forall A : Type, Bijective (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

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

Instance Bijective_Rinv :
  forall (A B : Type) (R : hrel A B),
    Bijective R -> Bijective (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma Rand_not_Bijective :
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

Lemma Ror_not_Bijective :
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

Lemma Rnot_not_Bijective :
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

(** * Rodzaje relacji homogenicznych *)

Definition rel (A : Type) : Type := hrel A A.

(** Relacje homogeniczne to takie, których wszystkie argumenty są tego
    samego typu. Warunek ten pozwala nam na wyrażenie całej gamy nowych
    właściwości, które relacje takie mogą posiadać.

    Uwaga terminologiczna: w innych pracach to, co nazwałem [Antireflexive]
    bywa zazwyczaj nazywane [Irreflexive]. Ja przyjąłem następujące reguły
    tworzenia nazw różnych rodzajów relacji:
    - "podstawowa" własność nie ma przedrostka, np. "zwrotna", "reflexive"
    - zanegowana własność ma przedrostek "nie" (lub podobny w nazwach
      angielskich), np. "niezwrotny", "irreflexive"
    - przeciwieństwo tej właściwości ma przedrostek "anty-" (po angielsku
      "anti-"), np. "antyzwrotna", "antireflexive" *)

(** ** Zwrotność *)

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

Instance Reflexive_empty :
  forall R : rel Empty_set, Reflexive R.
(* begin hide *)
Proof.
  split. destruct x.
Qed.
(* end hide *)

(** Okazuje się, że wszystkie relacje na [Empty_set] (a więc także na
    wszystkich innych typach pustych) są zwrotne. Nie powinno cię to w
    żaden sposób zaskakiwać — jest to tzw. pusta prawda (ang. vacuous
    truth), zgodnie z którą wszystkie zdania kwantyfikowane uniwersalnie
    po typie pustym są prawdziwe. Wszyscy w pustym pokoju są debilami. *)

Instance Reflexive_eq {A : Type} : Reflexive (@eq A).
(* begin hide *)
Proof.
  split. intro. apply eq_refl.
Qed.
(* end hide *)

Instance Reflexive_RTrue :
  forall A : Type, Reflexive (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma RFalse_nonempty_not_Reflexive :
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
  forall (A : Type) (R : rel A), Reflexive R ->
    subrelation (@eq A) R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Równość jest "najmniejszą" relacją zwrotną w tym sensie, że jest ona
    subrelacją każdej relacji zwrotnej. Intuicyjnym uzasadnieniem jest
    fakt, że w definicji [eq] poza konstruktorem [eq_refl], który daje
    zwrotność, nie ma niczego innego. *)

Instance Reflexive_Rcomp :
  forall (A : Type) (R S : rel A),
    Reflexive R -> Reflexive S -> Reflexive (Rcomp R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Instance Reflexive_Rinv :
  forall (A : Type) (R : rel A),
    Reflexive R -> Reflexive (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Instance Reflexive_Rand :
  forall (A : Type) (R S : rel A),
    Reflexive R -> Reflexive S -> Reflexive (Rand R S).
(* begin hide *)
Proof.
  destruct 1, 1. do 2 split; auto.
Qed.
(* end hide *)

Instance Reflexive_Ror :
  forall (A : Type) (R S : rel A),
    Reflexive R -> Reflexive (Ror R S).
(* begin hide *)
Proof.
  destruct 1. unfold Ror; split. auto.
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

Instance Antireflexive_neq :
  forall (A : Type), Antireflexive (fun x y : A => x <> y).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

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

Lemma Antireflexive_empty :
  forall R : rel Empty_set, Antireflexive R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma eq_nonempty_not_Antireflexive :
  forall A : Type, A -> ~ Antireflexive (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma RTrue_nonempty_not_Antireflexive :
  forall A : Type, A -> ~ Antireflexive (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

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

Lemma Rcomp_not_Antireflexive :
  exists (A : Type) (R S : rel A),
    Antireflexive R /\ Antireflexive S /\
    ~ Antireflexive (Rcomp R S).
(* begin hide *)
Proof.
  pose (R := fun b b' => b = negb b').
  exists bool, R, R. cut (Antireflexive R).
    Focus 2. rel. destruct x; inversion 1.
    rel. apply antireflexive0 with true. exists false. auto.
Qed.
(* end hide *)

Instance Antireflexive_Rinv :
  forall (A : Type) (R : rel A),
    Antireflexive R -> Antireflexive (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Instance Antireflexive_Rand :
  forall (A : Type) (R S : rel A),
    Antireflexive R -> Antireflexive (Rand R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

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

Instance Irreflexive_neq_nonempty :
  forall A : Type, A -> Irreflexive (Rnot (@eq A)).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

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

Lemma empty_not_Irreflexive :
  forall R : rel Empty_set, ~ Irreflexive R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma eq_empty_not_Irreflexive :
  ~ Irreflexive (@eq Empty_set).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma eq_nonempty_not_Irreflexive :
  forall A : Type, A -> ~ Irreflexive (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Równość jest zwrotna, a więc nie może być niezwrotna. Zauważ jednak,
    że musimy podać aż dwa osobne dowody tego faktu: jeden dla typu
    pustego [Empty_set], a drugi dla dowolnego typu niepustego. Wynika to
    z tego, że nie możemy sprawdzić, czy dowolny typ [A] jest pusty, czy
    też nie. *)

Lemma RTrue_empty_not_Irreflexive :
  ~ Irreflexive (@RTrue Empty_set Empty_set).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma RTrue_nonempty_not_Irreflexive :
  forall A : Type, A -> ~ Irreflexive (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma RFalse_empty_not_Irreflexive :
  ~ Irreflexive (@RFalse Empty_set Empty_set).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Instance Irreflexive_RFalse_nonempty :
  forall A : Type, A -> Irreflexive (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Podobnej techniki możemy użyć, aby pokazać, że relacja pełna ([RTrue])
    nie jest niezwrotna. Inaczej jest jednak w przypadku [RFalse] — na typie
    pustym nie jest ona niezwrotna, ale na dowolnym typie niepustym już
    owszem. *)

Lemma Rcomp_not_Irreflexive :
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

Instance Irreflexive_Rinv :
  forall (A : Type) (R : rel A),
    Irreflexive R -> Irreflexive (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Instance Irreflexive_Rand :
  forall (A : Type) (R S : rel A),
    Irreflexive R -> Irreflexive (Rand R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma Ror_not_Irreflexive :
  exists (A : Type) (R S : rel A),
    Irreflexive R /\ Irreflexive S /\ ~ Irreflexive (Ror R S).
(* begin hide *)
Proof.
  exists bool.
  pose (R := fun x y : bool => if x then x = negb y else x = y).
  pose (S := fun x y : bool => if x then x = y else x = negb y).
  exists R, S; unfold R, S; rel.
    exists true; cbn. inversion 1.
    exists false; cbn. inversion 1.
    destruct x; auto.
Qed.
(* end hide *)

(** Odwrotność relacji niezwrotnej jest niezwrotna. Koniunkcja dowolnej
    relacji z relacją niezwrotną daje relację niezwrotną. Tak więc za
    pomocą koniunkcji i dysjunkcji możemy łatwo dawać i zabierać
    zwrotność różnym relacjom. Okazuje się też, że dysjunkcja nie
    zachowuje niezwrotności.

    Na zakończenie zbadajmy jeszcze, jakie związki zachodzą pomiędzy
    zwrotnością, antyzwrotnością i niezwrotnością. *)

Instance Reflexive_Rnot :
  forall (A : Type) (R : rel A),
    Antireflexive R -> Reflexive (Rnot R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Instance Antireflexive_Rnot :
  forall (A : Type) (R : rel A),
    Reflexive R -> Antireflexive (Rnot R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Podstawowa zależność między nimi jest taka, że negacja relacji zwrotnej
    jest antyzwrotna, zaś negacja relacji antyzwrotnej jest zwrotna. *)

Lemma Reflexive_Antireflexive_empty :
  forall R : rel Empty_set, Reflexive R /\ Antireflexive R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma Reflexive_Antireflexive_nonempty :
  forall (A : Type) (R : rel A),
    A -> Reflexive R -> Antireflexive R -> False.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Każda relacja na typie pustym jest jednocześnie zwrotna i antyzwrotna,
    ale nie może taka być żadna relacja na typie niepustym. *)

Instance Irreflexive_nonempty_Antireflexive :
  forall (A : Type) (R : rel A),
    A -> Antireflexive R -> Irreflexive R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Związek między niezwrotnością i antyzwrotnością jest nadzwyczaj prosty:
    każda relacja antyzwrotna na typie niepustym jest też niezwrotna. *)

(** ** Symetria *)

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
    Symmetric R <-> same_hrel (Rinv R) R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Alterntywną charakteryzacją symetrii może być stwierdzenie, że relacja
    symetryczna to taka, która jest swoją własną odwrotnością. *)

Instance Symmetric_eq :
  forall A : Type, Symmetric (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Instance Symmetric_RTrue :
  forall A : Type, Symmetric (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Instance Symmetric_RFalse :
  forall A : Type, Symmetric (@RFalse A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Równość, relacja pełna i pusta są symetryczne. *)

Lemma Rcomp_not_Symmetric :
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
      Focus 2. unfold R, S in H. destruct x, H; cbn in *; congruence.
      exists true. unfold R, S. cbn. auto.
Qed.
(* end hide *)

(** Złożenie relacji symetrycznych nie musi być symetryczne. *)

Instance Symmetric_Rinv :
  forall (A : Type) (R : rel A),
    Symmetric R -> Symmetric (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Instance Symmetric_Rand :
  forall (A : Type) (R S : rel A ),
    Symmetric R -> Symmetric S -> Symmetric (Rand R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Instance Symmetric_Ror :
  forall (A : Type) (R S : rel A ),
    Symmetric R -> Symmetric S -> Symmetric (Ror R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Instance Symmetric_Rnot :
  forall (A : Type) (R : rel A ),
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

Lemma Antisymmetric_empty :
  forall R : rel Empty_set, Antisymmetric R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma eq_nonempty_not_Antisymmetric :
  forall A : Type, A -> ~ Antisymmetric (@eq A).
(* begin hide *)
Proof.
  intros A x. destruct 1. apply (antisymmetric0 x x); trivial.
Qed.
(* end hide *)

Lemma RTrue_nonempty_not_Antisymmetric :
  forall A : Type, A -> ~ Antisymmetric (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

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

Lemma Rcomp_not_Antisymmetric :
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

Instance Antisymmetric_Rinv :
  forall (A : Type) (R : rel A),
    Antisymmetric R -> Antisymmetric (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Instance Antisymmetric_Rand :
  forall (A : Type) (R S : rel A),
    Antisymmetric R -> Antisymmetric (Rand R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma Ror_not_Antisymmetric :
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

Lemma Rnot_not_Antisymmetric :
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

Lemma empty_not_Asymmetric :
  forall R : rel Empty_set, ~ Asymmetric R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma Rcomp_not_Asymmetric :
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

Instance Asymmetric_Rinv :
  forall (A : Type) (R : rel A),
    Asymmetric R -> Asymmetric (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma Rand_not_Asymmetric :
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

Lemma Ror_not_Asymmetric :
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

(** ** Przechodniość (TODO) *)

Class Transitive {A : Type} (R : rel A) : Prop :=
{
    transitive : forall x y z : A, R x y -> R y z -> R x z
}.

Instance Transitive_eq :
  forall A : Type, Transitive (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma Rcomp_not_Transitive :
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

Instance Transitive_Rinv :
  forall (A : Type) (R : rel A),
    Transitive R -> Transitive (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Instance Transitive_Rand :
  forall (A : Type) (R S : rel A),
    Transitive R -> Transitive S -> Transitive (Rand R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma Ror_not_Transitive :
  exists (A : Type) (R S : rel A),
    Transitive R /\ Transitive S /\ ~ Transitive (Ror R S).
(* begin hide *)
Proof.
  pose (R := fun b b' : bool => if b then True else False).
  pose (S := fun b b' : bool => if b' then True else False).
  exists bool, R, S. rel.
  specialize (transitive0 false true false). rel.
Qed.
(* end hide *)

Lemma Rnot_not_Transitive :
  exists (A : Type) (R : rel A),
    Transitive R /\ ~ Transitive (Rnot R).
(* begin hide *)
Proof.
  pose (R := fun b b' : bool => if andb b b' then True else False).
  exists bool, R. repeat split; intros.
    destruct x, y, z; compute in *; auto.
    unfold Rnot; destruct 1.
      eapply (transitive0 true false true); cbn; auto.
Qed.
(* end hide *)

(** ** Inne (TODO) *)

Class Total {A : Type} (R : rel A) : Prop :=
{
    total : forall x y : A, R x y \/ R y x
}.

(* begin hide *)
Lemma Rcomp_not_Total :
  exists (A : Type) (R S : rel A),
    Total R /\ Total S /\ ~ Total (Rcomp R S).
Proof.
  pose (R := fun n m : nat => orb (leb 1 n)
    (orb (leb 1 m) (lookup (n, m) [(0, n); (n, 0)])) = true).
  pose (S := fun n m : nat =>
    lookup (n, m) [(1, 2); (3, 4)] = true).
  exists nat, R, R. repeat split.
    destruct x as [| [| [|]]], y as [| [| [|]]]; compute; auto.
    destruct x as [| [| [|]]], y as [| [| [|]]]; compute; auto.
    unfold Rcomp; destruct 1.
      specialize (total0 2 1). decompose [and or ex] total0.
        compute in H. compute in H1. destruct x; cbn in H.
Restart.
  exists nat, le, le.
  split.
    admit.
    split.
      admit.
      destruct 1 as [T]. compute in T. cbn in T.
Abort.
(* end hide *)

Instance Total_Rinv :
  forall (A : Type) (R : rel A),
    Total R -> Total (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(* begin hide *)
Lemma Rand_not_Total :
  exists (A : Type) (R S : rel A),
    Total R /\ Total S /\ ~ Total (Rand R S).
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

Instance Total_Ror :
  forall (A : Type) (R S : rel A),
    Total R -> Total S -> Total (Ror R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma Rnot_not_Total :
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

Instance Total_Reflexive :
  forall (A : Type) (R : rel A),
    Total R -> Reflexive R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Class Trichotomous {A : Type} (R : rel A) : Prop :=
{
    trichotomous : forall x y : A, R x y \/ x = y \/ R y x
}.

Instance Trichotomous_empty :
  forall R : rel Empty_set, Trichotomous R.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Instance Trichotomous_eq_singleton :
  forall A : Type, (forall x y : A, x = y) -> Trichotomous (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Instance Total_Trichotomous :
  forall (A : Type) (R : rel A),
    Total R -> Trichotomous R.
(* begin hide *)
Proof.
  destruct 1. split. intros. destruct (total0 x y).
    left. assumption.
    do 2 right. assumption.
Qed.
(* end hide *)

Lemma eq_not_Trichotomous :
  exists A : Type, ~ Trichotomous (@eq A).
(* begin hide *)
Proof.
  exists bool. destruct 1. destruct (trichotomous0 true false); rel.
Qed.
(* end hide *)

(* begin hide *)
Require Import Lia.

Lemma Rcomp_not_Trichotomous :
  exists (A : Type) (R S : rel A),
    Trichotomous R /\ Trichotomous S /\ ~ Trichotomous (Rcomp R S).
Proof.
  exists nat, lt, lt. split; [idtac | split].
    1-2: split; lia.
    destruct 1. unfold Rcomp in *. specialize (trichotomous0 0 1).
      decompose [and or ex] trichotomous0; clear trichotomous0.
        all: lia.
Qed.
(* end hide *)

Instance Trichotomous_Rinv :
  forall (A : Type) (R : rel A),
    Trichotomous R -> Trichotomous (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(* begin hide *)
Lemma Rand_not_Trichotomous :
  exists (A : Type) (R S : rel A),
    Trichotomous R /\ Trichotomous S /\ ~ Trichotomous (Rand R S).
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

(* begin hide *)
Instance Trichotomous_Ror :
  forall (A : Type) (R S : rel A),
    Trichotomous R -> Trichotomous S -> Trichotomous (Ror R S).
Proof. rel. Qed.
(* end hide *)

Lemma Rnot_not_Trichotomous :
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

Class Dense {A : Type} (R : rel A) : Prop :=
{
    dense : forall x y : A, R x y -> exists z : A, R x z /\ R z y
}.

Instance Dense_eq :
  forall A : Type, Dense (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Instance Dense_Rinv :
  forall (A : Type) (R : rel A),
    Dense R -> Dense (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(* begin hide *)
Lemma Rcomp_not_Dense :
  exists (A : Type) (R S : rel A),
    Dense R /\ Dense S /\ ~ Dense (Rcomp R S).
Proof.
  (* TODO: Potrzebna jest dowolna relacja gęsta i antyzwrotna. *)
  exists nat.
  assert (R : rel nat). admit.
  assert (Dense R). admit.
  assert (Irreflexive R). admit.
  exists R, R. split; [assumption | split; [assumption | idtac]].
  destruct 1. unfold Rcomp in *.
Abort.
(* end hide *)

(* begin hide *)
Lemma Rand_not_Dense :
  exists (A : Type) (R S : rel A),
    Dense R /\ Dense S /\ ~ Dense (Rand R S).
Proof.
Abort.
(* end hide *)

Instance Dense_Ror :
  forall (A : Type) (R S : rel A),
    Dense R -> Dense S -> Dense (Ror R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(* begin hide *)
Lemma Rnot_not_Dense :
  exists (A : Type) (R : rel A),
    Dense R /\ ~ Dense (Rnot R).
Proof.
Abort.
(* end hide *)

(** * Relacje równoważności (TODO) *)

Class Equivalence {A : Type} (R : rel A) : Prop :=
{
    Equivalence_Reflexive :> Reflexive R;
    Equivalence_Symmetric :> Symmetric R;
    Equivalence_Transitive :> Transitive R;
}.

Instance Equivalence_eq :
  forall A : Type, Equivalence (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(* begin hide *)
Lemma Rcomp_Equivalence :
  forall (A : Type) (R S : rel A),
    Equivalence R -> Equivalence S -> Equivalence (Rcomp R S).
Proof.
  unfold Rcomp.
  destruct 1 as [[R1] [S1] [T1]],
           1 as [[R2] [S2] [T2]].
  repeat split; intros.
    rel.
    destruct H as (b & H1 & H2).
Abort.

Lemma Rcomp_not_Equivalence :
  exists (A : Type) (R S : rel A),
    Equivalence R /\ Equivalence S /\ ~ Equivalence (Rcomp R S).
Proof.
  exists
    (list nat),
    (fun l1 l2 => length l1 = length l2),
    (fun l1 l2 => nth 5 l1 = nth 5 l2).
  repeat split; intros.
    1-4: admit.
    destruct 1 as [[R] [S] [T]].
      specialize (T [1] [1; 4; 5; 1; 6] [1; 3]). unfold Rcomp in T. cbn in T.
Abort.
(* end hide *)

Instance Equivalence_Rinv :
  forall (A : Type) (R : rel A),
    Equivalence R -> Equivalence (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Instance Equivalence_Rand :
  forall (A : Type) (R S : rel A),
    Equivalence R -> Equivalence S -> Equivalence (Rand R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Inductive Threee : Type := One | Two | Three.

(* begin hide *)
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

Lemma Ror_not_Equivaence :
  exists (A : Type) (R S : rel A),
    Equivalence R /\ Equivalence S /\ ~ Equivalence (Ror R S).
Proof.
  exists
    (list nat),
    (fun l1 l2 => length l1 = length l2),
    (fun l1 l2 => head l1 = head l2).
  repeat split; intros.
    rewrite H. reflexivity.
    rewrite H, H0. reflexivity.
    rewrite H. reflexivity.
    rewrite H, H0. reflexivity.
    {
      destruct 1 as [R S T]. destruct T as [T].
      specialize (T [1] [2] [2; 3]).
      compute in T. specialize (T ltac:(auto) ltac:(auto)). destruct T; congruence.
    }
Qed.
(* end hide *)

(* begin hide *)
Lemma Rnot_not_Equivalence :
  exists (A : Type) (R : rel A),
    Equivalence R /\ ~ Equivalence (Rnot R).
Proof.
  exists
    bool,
    (fun b1 b2 => bool_eq b1 b2 = true).
  split.
    repeat constructor; destruct x; try destruct y; try destruct z; cbn; auto.
    destruct 1 as [[R] S T]. compute in R.
      specialize (R true). cbn in R. apply R. reflexivity.
Qed.
(* end hide *)

(** * Relacje apartheidu (TODO) *)

Class Apartness {A : Type} (R : A -> A -> Prop) : Prop :=
{
    Apartness_Antireflexive :> Antireflexive R;
    Apartness_Symmetric :> Symmetric R;
    Apartness_Cotransitive :
      forall x y : A, R x y -> forall z : A, R x z \/ R z y;
}.

Instance Apartness_Rinv :
  forall (A : Type) (R : rel A),
    Apartness R -> Apartness (Rinv R).
(* begin hide *)
Proof.
  destruct 1 as [[Anti] [Sym] Cotrans].
  split; try split; intros.
    intro. apply (Anti _ H).
    apply Sym. assumption.
    destruct (Cotrans _ _ H z).
      right. assumption.
      left. assumption.
Qed.
(* end hide *)

Instance Apartness_Ror :
  forall (A : Type) (R S : rel A),
    Apartness R -> Apartness S -> Apartness (Ror R S).
(* begin hide *)
Proof.
  destruct 1 as [[AntiR] [SymR] CotransR],
           1 as [[AntiS] [SymS] CotransS].
  split; try split; intros.
    intros []; firstorder.
    destruct H; red.
      left. apply SymR. assumption.
      right. apply SymS. assumption.
    destruct H.
      destruct (CotransR _ _ H z).
        left. left. assumption.
        right. left. assumption.
      destruct (CotransS _ _ H z).
        left. right. assumption.
        right. right. assumption.
Qed.
(* end hide *)

Lemma Apartness_not_Rand :
  exists (A : Type) (R S : rel A),
    Apartness R /\ Apartness S /\ ~ Apartness (Rand R S).
(* begin hide *)
Proof.
  exists
    (list (nat * nat)),
    (fun l1 l2 => map fst l1 <> map fst l2),
    (fun l1 l2 => map snd l1 <> map snd l2).
  split.
    repeat split; repeat intro.
      congruence.
      congruence.
      destruct (list_eq_dec Nat.eq_dec (map fst x) (map fst z)); subst.
        right. rewrite <- e. assumption.
        left. assumption.
  split.
    repeat split; repeat intro.
      congruence.
      congruence.
      destruct (list_eq_dec Nat.eq_dec (map snd x) (map snd z)); subst.
        right. rewrite <- e. assumption.
        left. assumption.
  destruct 1 as [[A] [S] C].
  unfold Rand in C.
  specialize (C [(1, 2)] [(2, 1)]); cbn in C.
  specialize (C ltac:(split; cbn in *; congruence) [(2, 2)]); cbn in C.
  decompose [and or] C; clear C; congruence.
Qed.
(* end hide *)

(** * Słabe relacje homogeniczne (TODO) *)

(* begin hide *)
(* TODO *) Class WeakReflexive {A : Type} {E : rel A}
  (H : Equivalence E) (R : rel A) : Prop :=
{
    wrefl : forall x y : A, R x y -> E x y
}.
(* end hide *)

Class Univalent {A : Type} (R : rel A) : Prop :=
{
    univalent : forall x y : A, R x y -> R y x -> x = y
}.

Instance Univalent_eq :
  forall A : Type, Univalent (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma Rcomp_not_Univalent :
  exists (A : Type) (R S : rel A),
    Univalent R /\ Univalent S /\
      ~ Univalent (Rcomp R S).
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
      apply univalent0.
        exists false. cbn. auto.
        exists false. cbn. auto.
Qed.
(* end hide *)

Instance Univalent_Rinv :
  forall (A : Type) (R : rel A),
    Univalent R -> Univalent (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Instance Univalent_Rand :
  forall (A : Type) (R S : rel A),
    Univalent R -> Univalent S ->
      Univalent (Rand R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma Ror_not_Univalent :
  exists (A : Type) (R S : rel A),
    Univalent R /\ Univalent S /\
      ~ Univalent (Ror R S).
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
      apply univalent0; cbn; auto.
Qed.
(* end hide *)

Lemma Rnot_not_Univalent :
  exists (A : Type) (R : rel A),
    Univalent R /\ ~ Univalent (Rnot R).
(* begin hide *)
Proof.
  pose (R := fun b b' : bool => if andb b b' then True else False).
  exists bool, R. repeat split; intros.
    destruct x, y; compute in *; intuition.
    unfold Rnot; destruct 1.
      cut (true = false).
        inversion 1.
        apply univalent0; auto.
Qed.
(* end hide *)

Class Univalent' {A : Type} {E : rel A}
  (H : Equivalence E) (R : rel A) : Prop :=
{
    wasym : forall x y : A, R x y -> R y x -> E x y
}.

Instance Univalent_equiv :
  forall (A : Type) (E : rel A) (H : Equivalence E),
    Univalent' H E.
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma Rcomp_not_Univalent' :
  exists (A : Type) (E R S : rel A), forall H : Equivalence E,
    Univalent' H R /\ Univalent' H S /\
      ~ Univalent' H (Rcomp R S).
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

Instance Univalent'_Rinv :
  forall (A : Type) (E : rel A) (H : Equivalence E) (R : rel A),
    Univalent' H R -> Univalent' H (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Instance Univalent'_Rand :
  forall (A : Type) (E : rel A) (H : Equivalence E) (R S : rel A),
    Univalent' H R -> Univalent' H S ->
      Univalent' H (Rand R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma Ror_not_Univalent' :
  exists (A : Type) (E R S : rel A), forall H : Equivalence E,
    Univalent' H R /\ Univalent' H S /\
      ~ Univalent' H (Ror R S).
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

Lemma Rnot_not_Univalent' :
  exists (A : Type) (E R : rel A), forall H : Equivalence E,
    Univalent' H R /\ ~ Univalent' H (Rnot R).
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

(** * Złożone relacje homogeniczne (TODO) *)

Class Preorder {A : Type} (R : rel A) : Prop :=
{
    Preorder_refl :> Reflexive R;
    Preorder_trans :> Transitive R;
}.

Class PartialOrder {A : Type} (R : rel A) : Prop :=
{
    PartialOrder_Preorder :> Preorder R;
    PartialOrder_Univalent :> Univalent R;
}.

Class TotalOrder {A : Type} (R : rel A) : Prop :=
{
    TotalOrder_PartialOrder :> PartialOrder R;
    TotalOrder_Total : Total R;
}.

Class StrictPreorder {A : Type} (R : rel A) : Prop :=
{
    StrictPreorder_Antireflexive :> Antireflexive R;
    StrictPreorder_Transitive :> Transitive R;
}.

Class StrictPartialOrder {A : Type} (R : rel A) : Prop :=
{
    StrictPartialOrder_Preorder :> StrictPreorder R;
    StrictPartialOrder_Univalent :> Antisymmetric R;
}.

Class StrictTotalOrder {A : Type} (R : rel A) : Prop :=
{
    StrictTotalOrder_PartialOrder :> StrictPartialOrder R;
    StrictTotalOrder_Total : Total R;
}.

(** * Domknięcia (TODO) *)

Require Import Classes.RelationClasses.

(** Uwaga, najnowszy pomysł: przedstawić domknięcia w taki sposób, żeby
    niepostrzeżenie przywyczajały do monad. *)

Class Closure
  {A : Type}
  (Cl : (A -> A -> Prop) -> (A -> A -> Prop)) : Prop :=
{
    pres :
      forall R S : A -> A -> Prop,
        (forall x y : A, R x y -> S x y) ->
          forall x y : A, Cl R x y -> Cl S x y;
    step :
      forall R : A -> A -> Prop,
        forall x y : A, R x y -> Cl R x y;
    join :
      forall R : A -> A -> Prop,
        forall x y : A, Cl (Cl R) x y -> Cl R x y;
}.

Inductive refl_clos {A : Type} (R : rel A) : rel A :=
    | rc_step : forall x y : A, R x y -> refl_clos R x y
    | rc_refl : forall x : A, refl_clos R x x.

#[refine]
Instance Closure_refl_clos {A : Type} : Closure (@refl_clos A) :=
{
    step := rc_step;
}.
Proof.
  induction 2.
    constructor. apply H. assumption.
    constructor 2.
  inversion 1; subst.
    assumption.
    constructor 2.
Qed.

(* begin hide *)
Hint Constructors refl_clos : core.

Ltac rc := compute; repeat split; intros; rel;
repeat match goal with
    | H : refl_clos _ _ _ |- _ => induction H; eauto
end; rel.
(* end hide *)

Instance Reflexive_rc :
  forall (A : Type) (R : rel A), Reflexive (refl_clos R).
(* begin hide *)
Proof. rc. Qed.
(* end hide *)

Lemma subrelation_rc :
  forall (A : Type) (R : rel A), subrelation R (refl_clos R).
(* begin hide *)
Proof. rc. Qed.
(* end hide *)

Lemma rc_smallest :
  forall (A : Type) (R S : rel A),
    subrelation R S -> Reflexive S -> subrelation (refl_clos R) S.
(* begin hide *)
Proof. rc. Qed.
(* end hide *)

Lemma rc_idempotent :
  forall (A : Type) (R : rel A),
    refl_clos (refl_clos R) <--> refl_clos R.
(* begin hide *)
Proof. rc. Qed.
(* end hide *)

Lemma rc_Rinv :
  forall (A : Type) (R : rel A),
    Rinv (refl_clos (Rinv R)) <--> refl_clos R.
(* begin hide *)
Proof. rc. Qed.
(* end hide *)

Inductive symm_clos {A : Type} (R : rel A) : rel A :=
    | sc_step :
        forall x y : A, R x y -> symm_clos R x y
    | sc_symm :
        forall x y : A, symm_clos R x y -> symm_clos R y x.

(* begin hide *)
Hint Constructors symm_clos : core.

Ltac sc := compute; repeat split; intros; rel;
repeat match goal with
    | H : symm_clos _ _ _ |- _ => induction H; eauto
end.
(* end hide *)

Instance Symmetric_sc :
  forall (A : Type) (R : rel A), Symmetric (symm_clos R).
(* begin hide *)
Proof. sc. Qed.
(* end hide *)

Lemma subrelation_sc :
  forall (A : Type) (R : rel A), subrelation R (symm_clos R).
(* begin hide *)
Proof. sc. Qed.
(* end hide *)

Lemma sc_smallest :
  forall (A : Type) (R S : rel A),
    subrelation R S -> Symmetric S -> subrelation (symm_clos R) S.
(* begin hide *)
Proof. sc. Qed.
(* end hide *)

Lemma sc_idempotent :
  forall (A : Type) (R : rel A),
    symm_clos (symm_clos R) <--> symm_clos R.
(* begin hide *)
Proof. sc. Qed.
(* end hide *)

Lemma sc_Rinv :
  forall (A : Type) (R : rel A),
    Rinv (symm_clos (Rinv R)) <--> symm_clos R.
(* begin hide *)
Proof. sc. Qed.
(* end hide *)

Inductive trans_clos {A : Type} (R : rel A) : rel A :=
    | tc_step :
        forall x y : A, R x y -> trans_clos R x y
    | tc_trans :
        forall x y z : A,
          trans_clos R x y -> trans_clos R y z -> trans_clos R x z.

(* begin hide *)
Hint Constructors trans_clos : core.

Ltac tc := compute; repeat split; intros; rel;
repeat match goal with
    | H : trans_clos _ _ _ |- _ => induction H; eauto
end.
(* end hide *)

Instance Transitive_tc :
  forall (A : Type) (R : rel A), Transitive (trans_clos R).
(* begin hide *)
Proof. tc. Qed.
(* end hide *)

Lemma subrelation_tc :
  forall (A : Type) (R : rel A), subrelation R (trans_clos R).
(* begin hide *)
Proof. tc. Qed.
(* end hide *)

Lemma tc_smallest :
  forall (A : Type) (R S : rel A),
    subrelation R S -> Transitive S ->
      subrelation (trans_clos R) S.
(* begin hide *)
Proof. tc. Qed.
(* end hide *)

Lemma tc_idempotent :
  forall (A : Type) (R : rel A),
    trans_clos (trans_clos R) <--> trans_clos R.
(* begin hide *)
Proof. tc. Qed.
(* end hide *)

Lemma tc_Rinv :
  forall (A : Type) (R : rel A),
    Rinv (trans_clos (Rinv R)) <--> trans_clos R.
(* begin hide *)
Proof. tc. Qed.
(* end hide *)

Inductive equiv_clos {A : Type} (R : rel A) : rel A :=
  | ec_step :
      forall x y : A, R x y -> equiv_clos R x y
  | ec_refl :
      forall x : A, equiv_clos R x x
  | ec_symm :
      forall x y : A, equiv_clos R x y -> equiv_clos R y x
  | ec_trans :
      forall x y z : A,
        equiv_clos R x y -> equiv_clos R y z -> equiv_clos R x z.

(* begin hide *)
Hint Constructors equiv_clos : core.

Ltac ec := compute; repeat split; intros; rel;
repeat match goal with
    | H : equiv_clos _ _ _ |- _ => induction H; eauto
end.
(* end hide *)

Instance Equivalence_ec :
  forall (A : Type) (R : rel A), Equivalence (equiv_clos R).
(* begin hide *)
Proof. ec. Qed.
(* end hide *)

Lemma subrelation_ec :
  forall (A : Type) (R : rel A), subrelation R (equiv_clos R).
(* begin hide *)
Proof. ec. Qed.
(* end hide *)

Lemma ec_smallest :
  forall (A : Type) (R S : rel A),
    subrelation R S -> Equivalence S ->
      subrelation (equiv_clos R) S.
(* begin hide *)
Proof. ec. Qed.
(* end hide *)

Lemma ec_idempotent :
  forall (A : Type) (R : rel A),
    equiv_clos (equiv_clos R) <--> equiv_clos R.
(* begin hide *)
Proof. ec. Qed.
(* end hide *)

Lemma ec_Rinv :
  forall (A : Type) (R : rel A),
    Rinv (equiv_clos (Rinv R)) <--> equiv_clos R.
(* begin hide *)
Proof. ec. Qed.
(* end hide *)

(** *** Domknięcie zwrotnosymetryczne *)

Definition rsc {A : Type} (R : rel A) : rel A :=
  refl_clos (symm_clos R).

(* begin hide *)
Ltac rstc := compute; repeat split; intros; rel;
repeat match goal with
    | H : refl_clos _ _ _ |- _ => induction H; eauto
    | H : symm_clos _ _ _ |- _ => induction H; eauto
    | H : trans_clos _ _ _ |- _ => induction H; eauto
end; rel.
(* end hide *)

Instance Reflexive_rsc :
  forall (A : Type) (R : rel A), Reflexive (rsc R).
(* begin hide *)
Proof. rstc. Qed.
(* end hide *)

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

(** *** Domknięcie równoważnościowe v2 *)

Definition rstc {A : Type} (R : rel A) : rel A :=
  trans_clos (symm_clos (refl_clos R)).

Instance Reflexive_rstc :
  forall {A : Type} (R : rel A),
    Reflexive (rstc R).
(* begin hide *)
Proof. rstc. Qed.
(* end hide *)

Instance Symmetric_rstc :
  forall {A : Type} (R : rel A),
    Symmetric (rstc R).
(* begin hide *)
Proof. rstc. Qed.
(* end hide *)

Instance Transitive_rstc :
  forall {A : Type} (R : rel A),
    Transitive (rstc R).
(* begin hide *)
Proof. rstc. Qed.
(* end hide *)

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

Lemma subrelation_rstc :
  forall (A : Type) (R : rel A), subrelation R (rstc R).
(* begin hide *)
Proof. rstc. Qed.
(* end hide *)

Lemma rstc_smallest :
  forall (A : Type) (R S : rel A),
    subrelation R S -> Equivalence S -> subrelation (rstc R) S.
(* begin hide *)
Proof. rstc. Qed.
(* end hide *)

Lemma refl_clos_rstc :
  forall {A : Type} (R : rel A),
    refl_clos (rstc R) <--> rstc R.
(* begin hide *)
Proof.
  split; red.
    inversion 1; subst.
      assumption.
      reflexivity.
    constructor. assumption.
Qed.
(* end hide *)

Lemma symm_clos_rstc :
  forall {A : Type} (R : rel A),
    symm_clos (rstc R) <--> rstc R.
(* begin hide *)
Proof.
  split; red.
    induction 1.
      assumption.
      symmetry. assumption.
    constructor. assumption.
Qed.
(* end hide *)

Lemma trans_clos_rstc :
  forall {A : Type} (R : rel A),
    trans_clos (rstc R) <--> rstc R.
(* begin hide *)
Proof.
  split; red.
    induction 1.
      assumption.
      rewrite IHtrans_clos1. assumption.
    constructor. assumption.
Qed.
(* end hide *)

Instance Equivalence_same_hrel :
  forall A B : Type,
    Equivalence (@same_hrel A B).
(* begin hide *)
Proof.
  split; red; intros.
    split; repeat intro; assumption.
    split; repeat intro; apply H; assumption.
    split; repeat intro.
      apply H0, H. assumption.
      apply H, H0. assumption.
Qed.
(* end hide *)

Lemma rstc_idempotent :
  forall (A : Type) (R : rel A),
    rstc (rstc R) <--> rstc R.
Proof.
  split.
    induction 1.
      induction H.
        induction H.
          assumption.
          reflexivity.
        symmetry. assumption.
      rewrite IHtrans_clos1. assumption.
    repeat intro. do 3 constructor. assumption.
Qed.
(* end hide *)

(* begin hide *)
Lemma rstc_Rinv :
  forall (A : Type) (R : rel A),
    Rinv (rstc (Rinv R)) <--> rstc R.
Proof.
  unfold Rinv. split; repeat intro.
    induction H.
      induction H.
        induction H.
          do 3 constructor. assumption.
          reflexivity.
        symmetry. assumption.
      rewrite IHtrans_clos2. assumption.
    induction H.
      induction H.
        induction H.
          do 3 constructor. assumption.
          reflexivity.
        symmetry. assumption.
      rewrite IHtrans_clos2. assumption.
Qed.
(* end hide *)

(** * Redukcje (TODO) *)

Definition rr {A : Type} (R : rel A) : rel A :=
  fun x y : A => R x y /\ x <> y.

Instance Antireflexive_rr :
  forall (A : Type) (R : rel A), Antireflexive (rr R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Require Import B3.

Lemma rr_rc :
  LEM ->
    forall (A : Type) (R : rel A),
      Reflexive R -> refl_clos (rr R) <--> R.
(* begin hide *)
Proof.
  intro lem. rc.
  destruct (lem (a = b)).
    subst. constructor 2.
    constructor. split; auto.
Qed.
(* end hide *)