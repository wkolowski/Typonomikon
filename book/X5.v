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

(** * Relacje binarne *)

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

Definition hrel (A B : Type) : Type := A -> B -> Prop.

(** Najważniejszym rodzajem relacji są relacje binarne, czyli relacje
    biorące dwa argumenty. To właśnie im poświęcimy ten rozdział, pominiemy
    zaś relacje biorące trzy i więcej argumentów. Określenia "relacja binarna"
    będę używał zarówno na określenie relacji binarnych heterogenicznych
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

(** * Operacje na relacjach *)

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

(** [Rinv] to operacja, która zamienia miejscami argumenty relacji. Relację
    [Rinv R] będziemy nazywać relacją odwrotną do [R]. *)

Theorem Rinv_Rcomp :
  forall (A B C : Type) (R : hrel A B) (S : hrel B C),
    same_hrel (Rinv (Rcomp R S)) (Rcomp (Rinv S) (Rinv R)).
(* begin hide *)
Proof.
  compute; split; intros; firstorder.
Qed.
(* end hide *)

Theorem Rinv_Rid :
  forall A : Type, same_hrel (@Rid A) (Rinv (@Rid A)).
(* begin hide *)
Proof. compute. firstorder. Qed.
(* end hide *)

(** Złożenie dwóch relacji możemy odwrócić, składając ich odwrotności w
    odwrotnej kolejności. Odwrotnością relacji identycznościowej jest
    zaś ona sama. *)

Definition Rnot {A B : Type} (R : hrel A B) : hrel A B :=
  fun (a : A) (b : B) => ~ R a b.

Definition Rand {A B : Type} (R S : hrel A B) : hrel A B :=
  fun (a : A) (b : B) => R a b /\ S a b.

Definition Ror {A B : Type} (R S : hrel A B) : hrel A B :=
  fun (a : A) (b : B) => R a b \/ S a b.

Definition Rdiff {A B : Type} (R S : hrel A B) : hrel A B :=
  fun (a : A) (b : B) => R a b /\ ~ S a b. (* TODO *)

(** Pozostałe trzy operacje na relacjach odpowiadają spójnikom logicznym —
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
  repeat split; intros; firstorder; subst; eauto.
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
  forall (A B : Type) (R S : hrel A B),
    Rand R S <--> Rand S R.
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

(** * Rodzaje relacji heterogenicznych *)

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

Instance LeftUnique_Rcomp :
  forall (A B C : Type) (R : hrel A B) (S : hrel B C),
    LeftUnique R -> LeftUnique S -> LeftUnique (Rcomp R S).
(* begin hide *)
Proof.
  wut. specialize (left_unique0 _ _ _ H0 H2). subst.
  apply left_unique1 with x0; assumption.
Qed.
(* end hide *)

Instance RightUnique_Rcomp :
  forall (A B C : Type) (R : hrel A B) (S : hrel B C),
    RightUnique R -> RightUnique S -> RightUnique (Rcomp R S).
(* begin hide *)
Proof.
  wut. specialize (right_unique1 _ _ _ H H1). subst.
  apply right_unique0 with x0; assumption.
Qed.
(* end hide *)

(** Składanie zachowuje oba rodzaje relacji unikalnych. TODO. *)

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

Instance LeftUnique_Rinv :
  forall (A B : Type) (R : hrel A B),
    RightUnique R -> LeftUnique (Rinv R).
(* begin hide *)
Proof.
  split. unfold Rinv; intros. apply right_unique with b; assumption.
Qed.
(* end hide *)

Instance RightUnique_Rinv :
  forall (A B : Type) (R : hrel A B),
    LeftUnique R -> RightUnique (Rinv R).
(* begin hide *)
Proof.
  split. unfold Rinv; intros. apply left_unique with a; assumption.
Qed.
(* end hide *)

(** Już na pierwszy rzut oka widać, że pojęcia te są w pewien sposób
    symetryczne. Aby uchwycić tę symetrię, możemy posłużyć się operacją
    [Rinv]. Okazuje się, że zamiana miejscami argumentów relacji lewostronnie
    unikalnej daje relację prawostronnie unikalną i vice versa. *)

Instance LeftUnique_Rand :
  forall (A B : Type) (R S : hrel A B),
    LeftUnique R -> LeftUnique (Rand R S).
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Instance RightUnique_Rand :
  forall (A B : Type) (R S : hrel A B),
    RightUnique R -> RightUnique (Rand R S).
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Theorem Ror_not_LeftUnique :
  exists (A B : Type) (R S : hrel A B),
    LeftUnique R /\ LeftUnique S /\ ~ LeftUnique (Ror R S).
(* begin hide *)
Proof.
  exists bool, bool.
  exists (@Rid bool), (fun b b' => b = negb b').
  wut. destruct 1.
  cut (true = false).
    inversion 1.
    apply left_unique0 with false; auto.
Qed.
(* end hide *)

Theorem Ror_not_RightUnique :
  exists (A B : Type) (R S : hrel A B),
    RightUnique R /\ RightUnique S /\ ~ RightUnique (Ror R S).
(* begin hide *)
Proof.
  exists bool, bool.
  exists (@Rid bool), (fun b b' => b = negb b').
  wut. destruct b, b'; cbn in H0; congruence. destruct 1.
  cut (true = false).
    inversion 1.
    apply right_unique0 with false; auto.
Qed.
(* end hide *)

(** Koniunkcja relacji unikalnej z inną daje relację unikalną, ale dysjunkcja
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
    są lewostronnie unikalne, to dodanie do [R] par z [S] może spowodować
    wystąpienie powtórzeń, co niszczy unikalność. *)

(** **** Ćwiczenie *)

(** Znajdź przykład relacji, która jest lewostronnie unikalna, ale nie jest
    prawostronnie unikalna.

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

Instance LeftTotal_Rcomp :
  forall (A B C : Type) (R : hrel A B) (S : hrel B C),
    LeftTotal R -> LeftTotal S -> LeftTotal (Rcomp R S).
(* begin hide *)
Proof.
  wut.
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
  wut. rename b into c.
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

(** Między lewo- i prawostronną totalnością występuje podobna symetria jak
    między dwoma formami unikalności: relacja odwrotna do lewostronnie
    totalnej jest prawostronnie totalna i vice versa. Totalność również
    jest zachowywana przez składanie. *)

Theorem LeftTotal_Ror :
  forall (A B : Type) (R S : hrel A B),
    LeftTotal R -> LeftTotal (Ror R S).
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Theorem RightTotal_Ror :
  forall (A B : Type) (R S : hrel A B),
    RightTotal R -> RightTotal (Ror R S).
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Theorem Rand_not_LeftTotal :
  exists (A B : Type) (R S : hrel A B),
    LeftTotal R /\ LeftTotal S /\ ~ LeftTotal (Rand R S).
(* begin hide *)
Proof.
  exists bool, bool.
  exists (@Rid bool), (fun b b' => b = negb b').
  wut.
    exists (negb a). destruct a; trivial.
    destruct 1. destruct (left_total0 true).
      destruct x, H; cbn in H0; try congruence.
Qed.
(* end hide *)

Theorem Rand_not_RightTotal :
  exists (A B : Type) (R S : hrel A B),
    RightTotal R /\ RightTotal S /\ ~ RightTotal (Rand R S).
(* begin hide *)
Proof.
  exists bool, bool.
  exists (@Rid bool), (fun b b' => b = negb b').
  wut.
    destruct 1. destruct (right_total0 true).
      destruct x, H; cbn in H0; try congruence.
Qed.
(* end hide *)

(** Związki totalności z koniunkcją i dysjunkcją relacji są podobne jak
    w przypadku unikalności, lecz tym razem to dysjunkcja zachowuje
    właściwość, a koniunkcja ją niszczy. Wynika to z tego, że dysjunkcja
    nie zabiera żadnych par z relacji, więc nie może uszkodzić totalności.
    Z drugiej strony koniunkcja może zabrać jakąś parę, a wtedy relacja
    przestaje być totalna. *)

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

Class Functional {A B : Type} (R : hrel A B) : Prop :=
{
    F_LT :> LeftTotal R;
    F_RU :> RightUnique R;
}.

(** Lewostronną totalność i prawostronną unikalność możemy połączyć, by
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

Definition Functional_to_fun
  {A B : Type} (R : hrel A B) (F : Functional R) : A -> B.
Proof.
  intro a. destruct F. destruct F_LT0.
  Fail destruct (left_total0 a).
Abort.

(** Z każdej funkcji można w prosty sposób zrobić relację funkcyjną, ale
    bez dodatkowych aksjomatów nie jesteśmy w stanie z relacji funkcyjnej
    zrobić funkcji. Przemilczając kwestie aksjomatów możemy powiedzieć
    więc, że relacje funkcyjne odpowiadają funkcjom.

    Co więcej, relacje funkcyjne, która są lewostronnie unikalne odpowiadają
    funkcjom injektywnym, a te które są prawostronnie totalne — funkcjom
    surjektywnym. Relacje spełniające wszystkie cztery warunki odpowiadają
    bijekcjom. *)

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

(** Złożenie relacji funkcyjnych również jest relacją funkcyjną. Nie powinno
    nas to dziwić — wszakże relacje funkcyjne odpowiadają funkcjom, a złożenie
    funkcji jest przecież funkcją. Jeżeli lepiej mu się przyjrzeć, to okazuje
    się, że składanie funkcji odpowiada składaniu relacji, a stąd już prosta
    droga do wniosku, że złożenie relacji funkcyjnych jest relacją funkcyjną. *)

Theorem Rinv_not_Functional :
  exists (A B : Type) (R : hrel A B),
    Functional R /\ ~ Functional (Rinv R).
(* begin hide *)
Proof.
  exists bool, bool, (fun b b' => b' = true). split.
    wut.
    destruct 1. destruct F_LT0. destruct (left_total0 false) as [b H].
      destruct b; inversion H.
Qed.
(* end hide *)

(** Odwrotność relacji funkcyjnej nie musi być funkcyjna. Dobrą wizualicją
    tego faktu może być np. funkcja f(x) = x^2 na liczbach rzeczywistych.
    Z pewnością jest to funkcja, a zatem relacja funkcyjna. Widać to na jej
    wykresie — każdemu punktowi dziedziny odpowiada dokładnie jeden punkt
    przeciwdziedziny. Jednak po wykonaniu operacji [Rinv], której odpowiada
    tutaj obrócenie układu współrzędnych o 90 stopni, nie otrzymujemy wcale
    wykresu funkcji. Wprost przeciwnie — niektórym punktom z osi X na takim
    wykresie odpowiadają dwa punkty na osi Y (np. punktowi 4 odpowiadają 2
    i -2). Stąd wnioskujemy, że odwrócenie relacji funkcyjnej f nie daje w
    wyniku relacji funkcyjnej. *)

Theorem Rand_not_Functional :
  exists (A B : Type) (R S : hrel A B),
    Functional R /\ Functional S /\ ~ Functional (Rand R S).
(* begin hide *)
Proof.
  exists bool, bool.
  exists (@Rid bool), (fun b b' => b = negb b').
  wut.
    exists (negb a). destruct a; trivial.
    destruct b, b'; cbn in H0; congruence.
    destruct 1. destruct F_LT0. destruct (left_total0 true).
      destruct x, H; cbn in H0; congruence.
Qed.
(* end hide *)

Theorem Ror_not_Functional :
  exists (A B : Type) (R S : hrel A B),
    Functional R /\ Functional S /\ ~ Functional (Ror R S).
(* begin hide *)
Proof.
  exists bool, bool.
  exists (@Rid bool), (fun b b' => b = negb b').
  wut.
    exists (negb a). destruct a; trivial.
    destruct b, b'; cbn in H0; congruence.
    destruct 1. destruct F_RU0.
      cut (false = true).
        inversion 1.
        apply right_unique0 with false; auto.
Qed.
(* end hide *)

(** Ani koniunkcje, ani dysjunkcje relacji funkcyjnych nie muszą być wcale
    relacjami funkcyjnymi. Jest to po części konsekwencją właściwości
    relacji lewostronnie totalnych i prawostronnie unikalnych: pierwsze
    mają problem z [Rand], a drugie z [Ror]. *)

(** **** Ćwiczenie *)

(** Możesz zadawać sobie pytanie: po co nam w ogóle pojęcie relacji
    funkcyjnej, skoro mamy funkcje? Funkcje muszą być obliczalne (ang.
    computable) i to na mocy definicji, zaś relacje — niekonieczne.
    Czasem prościej może być najpierw zdefiniować relację, a dopiero
    później pokazać, że jest funkcyjna. Czasem zdefiniowanie danego
    bytu jako funkcji może być niemożliwe.

    Funkcję Collatza klasycznie definiuje się w ten sposób: jeżeli n
    jest parzyste, to f(n) = n/2. W przeciwnym przypadku f(n) = 3n + 1.

    Zaimplementuj tę funkcję w Coqu. Spróbuj zaimplementować ją zarówno
    jako funkcję rekurencyjną, jak i relację. Czy twoja funkcja dokładnie
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

Compute map (collatz' 1000) [1; 2; 3; 4; 5; 6; 7; 8; 9].
Compute collatz' 1000 2487.

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
(* end hide *)

(** * Rodzaje relacji homogenicznych *)

Definition rel (A : Type) : Type := hrel A A.

(** Relacje homogeniczne to takie, których wszystkie argumenty są tego
    samego typu. Warunek ten pozwala nam na wyrażenie całej gamy nowych
    właściwości, które relacje takie mogą posiadać. *)

Class Reflexive {A : Type} (R : rel A) : Prop :=
{
    reflexive : forall x : A, R x x
}.

(** Relacja [R] jest zwrotna (ang. reflexive), jeżeli każdy [x : A] jest
    w relacji sam ze sobą. *)

Instance Reflexive_eq {A : Type} : Reflexive (@eq A).
(* begin hide *)
Proof.
  split. intro. apply eq_refl.
Qed.
(* end hide *)

(** Najważniejszym przykładem relacji zwrotnej jest równość. Przypomnij
    sobie, że [eq] ma tylko jeden konstruktor [eq_refl], który głosi,
    że każdy obiekt jest równy samemu sobie. *)

Theorem eq_subrelation_Reflexive :
  forall (A : Type) (R : rel A), Reflexive R ->
    subrelation (@eq A) R.
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

(** Równość jest "najmniejszą" relacją zwrotną w tym sensie, że jest ona
    subrelacją każdej relacji zwrotnej. Intuicyjnym uzasadnieniem jest
    fakt, że w definicji [eq] poza konstruktorem [eq_refl], który daje
    zwrotność, nie ma niczego innego. *)

Instance Reflexive_empty :
  forall R : rel Empty_set, Reflexive R.
(* begin hide *)
Proof.
  split. destruct x.
Qed.
(* end hide *)

(** Okazuje się, że wszystkie relacje na [Empty_set] (a więc także na
    wszystkich innych typach pustych) są zwrotne. Nie powinno cię to w
    żaden sposób zaskakiwać — jest to tzw. pusta prawda (ang. vacuous
    truth), zgodnie z którą wszystkie zdania kwantyfikowane uniwersalnie
    po typie pustym są prawdziwe. Wszyscy w pustym pokoju są debilami. *)

Theorem Reflexive_Rcomp :
  forall (A : Type) (R S : rel A),
    Reflexive R -> Reflexive S -> Reflexive (Rcomp R S).
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

(** Złożenie relacji zwrotnych jest relacją zwrotną. Dowód jest tak prosty,
    że nie ma sensu nawet próbować uzasdniać to intuicyjnie. *)

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

(** Jak widać, koniunkcja relacji zwrotnych także jest zwrotna. Dysjunkcja
    posiada natomiast dużo mocniejszą właściwość: dysjunkcja dowolnej relacji
    z relacją zwrotną daje relację zwrotną. Tak więc dysjunkcja [R] z [eq]
    pozwala nam łatwo "dodać" zwrotność do [R]. Słownie dysjunkcja z [eq]
    odpowiada zwrotowi "lub równy", który możemy spotkać np. w wyrażeniach
    "mniejszy lub równy", "większy lub równy". *)

Class Irreflexive {A : Type} (R : rel A) : Prop :=
{
    irreflexive : exists x : A, ~ R x x
}.

Class Antireflexive {A : Type} (R : rel A) : Prop :=
{
    antireflexive : forall x : A, ~ R x x
}.

(** Kolejne dwie właściwości to pochodne zwrotności. Relacja niezwrotna to
    taka, która nie jest zwrotna. Relacja antyzwrotna to taka, że żaden
    [x : A] nie jest w relacji sam ze sobą. Zauważ, że pojęcia te zasadniczo
    różnią się od siebie.

    Uwaga terminologiczna: w innych pracach to, co nazwaliśmy [Antireflexive]
    bywa zazwyczaj nazywane [Irreflexive]. Ja przyjąłem następujące reguły
    tworzenia nazw różnych rodzajów relacji:
    - "podstawowa" własność nie ma przedrostka, np. "zwrotna", "reflexive"
    - zanegowana własność ma przedrostek "nie" (lub podobny w nazwach
      angielskich), np. "niezwrotny", "irreflexive"
    - przeciwieństwo tej właściwości ma przedrostek "anty-" (po angielsku
      "anti-"), np. "antyzwrotna", "antireflexive" *)

Theorem Rcomp_not_Irreflexive :
  exists (A : Type) (R S : rel A),
    Irreflexive R /\ Irreflexive S /\ ~ Irreflexive (Rcomp R S).
(* begin hide *)
Proof.
  exists bool. pose (R := fun b b' => b = negb b').
  exists R, R. cut (Irreflexive R).
    Focus 2. split. exists true. unfold R. inversion 1.
    wut. destruct 1 as [[b Hb]]. apply Hb. destruct b.
      exists false. unfold R. auto.
      exists true. unfold R. auto.
Qed.
(* end hide *)

Instance Irreflexive_Rand :
  forall (A : Type) (R S : rel A),
    Irreflexive R -> Irreflexive (Rand R S).
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Theorem Ror_not_Irreflexive :
  exists (A : Type) (R S : rel A),
    Irreflexive R /\ Irreflexive S /\ ~ Irreflexive (Ror R S).
(* begin hide *)
Proof.
  exists bool.
  pose (R := fun x y : bool => if x then x = negb y else x = y).
  pose (S := fun x y : bool => if x then x = y else x = negb y).
  exists R, S; unfold R, S; wut.
    exists true; cbn. inversion 1.
    exists false; cbn. inversion 1.
    destruct 1. destruct irreflexive0 as [b H]. apply H. destruct b; auto.
Qed.
(* end hide *)

(** Koniunkcja dowolnej relacji z relacją niezwrotną daje relację niezwrotną.
    Tak więc za pomocą koniunkcji i dysjunkcji możemy łatwo "dodawać" i
    "odbierać" zwrotność różnym relacjom. Okazuje się też, że dysjunkcja nie
    zachowuje niezwrotności. *)

Theorem Antireflexive_empty :
  forall R : rel Empty_set, Antireflexive R.
(* begin hide *)
Proof.
  split. destruct x.
Qed.
(* end hide *)

Theorem eq_nonempty_not_Antireflexive :
  forall A : Type, A -> ~ Antireflexive (@eq A).
(* begin hide *)
Proof. wut. Qed.
(* end hid e*)

Instance Antireflexive_neq :
  forall (A : Type), Antireflexive (fun x y : A => x <> y).
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Theorem Rcomp_not_Antireflexive :
  exists (A : Type) (R S : rel A),
    Antireflexive R /\ Antireflexive S /\ ~ Antireflexive (Rcomp R S).
(* begin hide *)
Proof.
  pose (R := fun b b' => b = negb b').
  exists bool, R, R. cut (Antireflexive R).
    Focus 2. split. unfold R. destruct x; inversion 1.
    wut. destruct 1. apply antireflexive1 with true.
      exists false. unfold R. auto.
Qed.
(* end hide *)

Instance Antireflexive_Rand :
  forall (A : Type) (R S : rel A),
    Antireflexive R -> Antireflexive (Rand R S).
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Instance Antireflexive_Ror :
  forall (A : Type) (R S : rel A),
    Antireflexive R -> Antireflexive S -> Antireflexive (Ror R S).
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Instance Antireflexive_Rnot_nonempty :
  forall (A : Type) (nonempty : A) (R : rel A),
    Reflexive R -> Antireflexive (Rnot R).
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

(** Podobnie jak w przypadku relacji zwrotnych, każda relacja na typie
    pustym jest antyzwrotna, sztampowym zaś przykładem relacji antyzwrotnej
    jest nierówność [<>]. Ze względu na sposób działania ludzkiego mózgu
    antyzwrotna jest cała masa relacji znanych nam z codziennego życia:
    "bycie matką", "bycie ojcem", "bycie synem", "bycie córką", "bycie nad",
    "byciem pod", "bycie za", "bycie przed", etc.

    Koniunkcja dowolnej relacji z relacją antyzwrotną daje nam relację
    antyzwrotną, zaś dysjunkcja jedynie zachowuje właściwość bycia relacją
    antyzwrotną.

    Dzięki ostatniemu twierdzeniu widać też, czym naprawdę są właściwości
    poprzedzone przedrostkiem "anty-": negacja relacji zwrotnej jest
    antyzwrotna. *)

Class Symmetric {A : Type} (R : rel A) : Prop :=
{
    symmetric : forall x y : A, R x y -> R y x
}.

(** Relacja jest symetryczna, jeżeli kolejność podawania argumentów nie
    ma znaczenia. Przykładami ze świata rzeczywistego mogą być np. relacje
    "jest blisko", "jest obok", "jest naprzeciwko". *)

Instance Symmetric_eq :
  forall A : Type, Symmetric (@eq A).
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Theorem Rcomp_not_Symmetric :
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

Instance Symmetric_Rinv :
  forall (A : Type) (R : rel A),
    Symmetric R -> Symmetric (Rinv R).
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Theorem Symmetric_Rand :
  forall (A : Type) (R S : rel A ),
    Symmetric R -> Symmetric S -> Symmetric (Rand R S).
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Theorem Symmetric_Ror :
  forall (A : Type) (R S : rel A ),
    Symmetric R -> Symmetric S -> Symmetric (Ror R S).
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Theorem Symmetric_Rnot :
  forall (A : Type) (R : rel A ),
    Symmetric R -> Symmetric (Rnot R).
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

(** Symetria jest zachowywana zarówno przez koniunkcję i dysjunkcję, jak
    i przez negację. *)

Class Asymmetric {A : Type} (R : rel A) : Prop :=
{
    asymmetric : exists x y : A, R x y /\ ~ R y x
}.

Theorem empty_not_Asymmetric :
  forall R : rel Empty_set, ~ Asymmetric R.
(* begin hide *)
Proof.
  unfold not. wut. destruct x.
Qed.
(* end hide *)

Theorem Rcomp_not_Asymmetric :
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
Proof. wut. Qed.
(* end hide *)

Theorem Rand_not_Asymmetric :
  exists (A : Type) (R S : rel A),
    Asymmetric R /\ Asymmetric S /\ ~ Asymmetric (Rand R S).
(* begin hide *)
Proof.
  pose (R := fun b b' : bool => if b then b = negb b' else False).
  pose (S := fun b b' : bool => if negb b' then b = negb b' else False).
  exists bool, R, S. repeat split.
    exists true, false. cbn. auto.
    exists true, false. cbn. auto.
    unfold Rand; destruct 1.
      destruct asymmetric0 as [b1 [b2 [[H1 H2] H3]]].
      destruct b1, b2; cbn in *; intuition.
Abort.
(* end hide *)

Theorem Ror_not_Asymmetric :
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

Class Antisymmetric {A : Type} (R : rel A) : Prop :=
{
    antisymmetric : forall x y : A, R x y -> ~ R x y
}.

Theorem Antisymmetric_empty :
  forall R : rel Empty_set, Antisymmetric R.
(* begin hide *)
Proof. wut. destruct x. Qed.
(* end hide *)

Theorem eq_nonempty_not_Antisymmetric :
  forall A : Type, A -> ~ Antisymmetric (@eq A).
(* begin hide *)
Proof.
  intros A x. destruct 1. apply (antisymmetric0 x x); trivial.
Qed.
(* end hide *)

Instance Antisymmetric_Rcomp :
  forall (A : Type) (R S : rel A),
    Antisymmetric R -> Antisymmetric S -> Antisymmetric (Rcomp R S).
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Instance Antisymmetric_Rinv :
  forall (A : Type) (R : rel A),
    Antisymmetric R -> Antisymmetric (Rinv R).
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Instance Antisymmetric_Rand :
  forall (A : Type) (R S : rel A),
    Antisymmetric R -> Antisymmetric S -> Antisymmetric (Rand R S).
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Instance Antisymmetric_Ror :
  forall (A : Type) (R S : rel A),
    Antisymmetric R -> Antisymmetric S -> Antisymmetric (Ror R S).
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Goal
  forall (A : Type) (R : rel A),
    Antisymmetric R -> Antisymmetric (Rnot R).
Proof.
  wut. intro.
Abort.

Theorem Rnot_not_Antisymmetric :
  exists (A : Type) (R : rel A),
    Antisymmetric R /\ ~ Antisymmetric (Rnot R).
(* begin hide *)
Proof.
  pose (R := fun b b' : bool => b = negb b').
  exists bool, R. repeat split; intros.
    destruct x, y; compute in *; intuition.
Abort.
(* end hide *)

Class WeakAntisymmetric {A : Type} (R : rel A) : Prop :=
{
    wantisymmetric : forall x y : A, R x y -> R y x -> x = y
}.

Instance WeakAntisymmetric_eq :
  forall A : Type, WeakAntisymmetric (@eq A).
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Theorem Rcomp_not_WeakAntisymmetric :
  exists (A : Type) (R S : rel A),
    WeakAntisymmetric R /\ WeakAntisymmetric S /\
      ~ WeakAntisymmetric (Rcomp R S).
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
      apply wantisymmetric0.
        exists false. cbn. auto.
        exists false. cbn. auto.
Qed.
(* end hide *)

Instance WeakAntisymmetric_Rinv :
  forall (A : Type) (R : rel A),
    WeakAntisymmetric R -> WeakAntisymmetric (Rinv R).
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Instance WeakAntisymmetric_Rand :
  forall (A : Type) (R S : rel A),
    WeakAntisymmetric R -> WeakAntisymmetric S ->
      WeakAntisymmetric (Rand R S).
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Theorem Ror_not_WeakAntisymmetric :
  exists (A : Type) (R S : rel A),
    WeakAntisymmetric R /\ WeakAntisymmetric S /\
      ~ WeakAntisymmetric (Ror R S).
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
      apply wantisymmetric0; cbn; auto.
Qed.
(* end hide *)

Theorem Rnot_not_WeakAntisymmetric :
  exists (A : Type) (R : rel A),
    WeakAntisymmetric R /\ ~ WeakAntisymmetric (Rnot R).
(* begin hide *)
Proof.
  pose (R := fun b b' : bool => if andb b b' then True else False).
  exists bool, R. repeat split; intros.
    destruct x, y; compute in *; intuition.
    unfold Rnot; destruct 1.
      cut (true = false).
        inversion 1.
        apply wantisymmetric0; auto.
Qed.
(* end hide *)

Class Transitive {A : Type} (R : rel A) : Prop :=
{
    transitive : forall x y z : A, R x y -> R y z -> R x z
}.

Instance Transitive_eq :
  forall A : Type, Transitive (@eq A).
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Theorem Rcomp_not_Transitive :
  exists (A : Type) (R S : rel A),
    Transitive R /\ Transitive S /\ ~ Transitive (Rcomp R S).
(* begin hide *)
Proof.
  pose (R := fun b b' : option bool =>
    match b, b' with
      | None, _ => True
      | _, _ => False
    end).
  pose (S := fun b b' : option bool =>
    match b, b' with
      | Some _, _ => True
      | _, _ => False
    end).
  exists (option bool), R, S. repeat split; intros.
    destruct x as [[] |], y as [[] |], z as [[] |]; cbn in *; intuition.
    destruct x as [[] |], y as [[] |], z as [[] |]; cbn in *; intuition.
    unfold Rcomp; destruct 1.
      destruct (transitive0 None (Some true) None).
        exists (Some true). cbn. auto.
Abort.
(* end hide *)

Instance Transitive_Rinv :
  forall (A : Type) (R : rel A),
    Transitive R -> Transitive (Rinv R).
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Instance Transitive_Rand :
  forall (A : Type) (R S : rel A),
    Transitive R -> Transitive S -> Transitive (Rand R S).
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Theorem Ror_not_Transitive :
  exists (A : Type) (R S : rel A),
    Transitive R /\ Transitive S /\ ~ Transitive (Ror R S).
(* begin hide *)
Proof.
  pose (R := fun b b' : bool => if b then True else False).
  pose (S := fun b b' : bool => if b' then True else False).
  exists bool, R, S. wut. destruct 1.
  specialize (transitive0 false true false). cbn in *.
  destruct transitive0; firstorder.
Qed.
(* end hide *)

Theorem Rnot_not_Transitive :
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

Class Total {A : Type} (R : rel A) : Prop :=
{
    total : forall x y : A, R x y \/ R y x
}.

Theorem Rcomp_not_Total :
  exists (A : Type) (R S : rel A),
    Total R /\ Total S /\ ~ Total (Rcomp R S).
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
  exists bool, R, R. repeat split; intros.
    destruct x, y; cbn; auto.
    destruct x, y; cbn; auto.
    unfold Rcomp; destruct 1.
      destruct (total0 true false) as [[b H] | [b H]].
Abort.
(* end hide *)

Instance Total_Rinv :
  forall (A : Type) (R : rel A),
    Total R -> Total (Rinv R).
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Theorem Rand_not_Total :
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
  exists bool, R, R. repeat split; intros.
    destruct x, y; cbn; auto.
    destruct x, y; cbn; auto.
    unfold Rand; destruct 1.
Abort.
(* end hide *)

Instance Total_Ror :
  forall (A : Type) (R S : rel A),
    Total R -> Total S -> Total (Ror R S).
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Theorem Rnot_not_Total :
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
Proof. wut. Qed.
(* end hide *)

Class Trichotomous {A : Type} (R : rel A) : Prop :=
{
    trichotomous : forall x y : A, R x y \/ x = y \/ R y x
}.

Instance Trichotomous_eq :
  forall A : Type, Trichotomous (@eq A).
(* begin hide *)
Proof.
(* TODO *)
Abort.
(* end hide *)

Theorem Rcomp_not_Trichotomous :
  exists (A : Type) (R S : rel A),
    Trichotomous R /\ Trichotomous S /\ Trichotomous (Rcomp R S).
(* begin hide *)
Proof.
  pose (R := fun b b' : bool => b = negb b').
Abort.
(* end hide *)

Instance Trichotomous_Rinv :
  forall (A : Type) (R : rel A),
    Trichotomous R -> Trichotomous (Rinv R).
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Theorem Rand_not_Trichotomous :
  exists (A : Type) (R S : rel A),
    Trichotomous R /\ Trichotomous S /\ Trichotomous (Rand R S).
(* begin hide *)
Proof.
  pose (R := fun b b' : bool => b = negb b').
Abort.
(* end hide *)

Instance Trichotomous_Ror :
  forall (A : Type) (R S : rel A),
    Trichotomous R -> Trichotomous S -> Trichotomous (Ror R S).
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Theorem Rnot_not_Trichotomous :
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
Proof. wut. Qed.
(* end hide *)

Theorem Rcomp_not_Dense :
  exists (A : Type) (R S : rel A),
    Dense R /\ Dense S /\ ~ Dense (Rcomp R S).
(* begin hide *)
Proof.
Abort.
(* end hide *)

Instance Dense_Rinv :
  forall (A : Type) (R : rel A),
    Dense R -> Dense (Rinv R).
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Theorem Rand_not_Dense :
  exists (A : Type) (R S : rel A),
    Dense R /\ Dense S /\ ~ Dense (Rand R S).
(* begin hide *)
Proof.
Abort.
(* end hide *)

Instance Dense_Ror :
  forall (A : Type) (R S : rel A),
    Dense R -> Dense S -> Dense (Ror R S).
(* begin hide *)
Proof. wut. Qed.
(* end hide *)

Theorem Rnot_not_Dense :
  exists (A : Type) (R : rel A),
    Dense R /\ ~ Dense (Rnot R).
(* begin hide *)
Proof.
Abort.
(* end hide *)