(** * H3a: Relacje [TODO] *)

Require Import FunctionalExtensionality Nat Arith Lia.

Require Import List.
Import ListNotations.

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
    one po nich wszystkie ich właściwości. Fenomen ten nie jest w żaden
    sposób specyficzny dla relacji i operacji na nich - z pewnością spotkamy
    się z nim ponownie w nadchodzących rozdziałach. *)

(** * Relatory, czyli więcej operacji na relacjach (TODO) *)

(** Póki co wszystkie operacje na relacjach, które widzieliśmy, pochodziły po
    prostu od spójników logicznych. Co jednak z operacjami na typach, takimi
    jak produkt, suma, opcja, typy funkcyjne, etc.? Czy żyją one w odizolowanym
    świecie, który nie ma zupełnie żadnego związku ze światem relacji? Oczywiście,
    że nie: mając relacje na jakichś typach, możemy przekształcić je na relację na
    produkcie czy sumie tych typów w kanoniczny sposób spełniający pewne właściwości.
    Operacje, które dokonują tego przekształcenia, nazywać będziemy relatorami. *)

Class Relator (F : Type -> Type) : Type :=
{
  relate : forall {A : Type}, (A -> A -> Prop) -> (F A -> F A -> Prop);
  relate_id : forall {A : Type} (x y : F A), relate (@eq A) x y <-> eq x y;
}.

(** Przykładem relatora jest [option]. *)

#[export]
#[refine]
Instance Relator_option : Relator option :=
{
  relate := fun A R o1 o2 =>
    match o1, o2 with
    | Some a1, Some a2 => R a1 a2
    | None   , None    => True
    | _      , _       => False
    end;
}.
Proof.
  intros A [a1 |] [a2 |]; only 4: easy.
  - now split; [intros -> | intros [=]].
  - now split; [| congruence].
  - now split; [| congruence ].
Defined.

(** Możemy też zdefiniować pojęcia birelatora (od łacińskiego prefiksu "bi"
    oznaczającego "dwa"), czyli dwuargumentowy relator. *)

Class Birelator (F : Type -> Type -> Type) : Type :=
{
  birelate : forall {A B : Type}, (A -> A -> Prop) -> (B -> B -> Prop) -> (F A B -> F A B -> Prop);
  birelate_id : forall {A B : Type} (x y : F A B), birelate (@eq A) (@eq B) x y <-> eq x y;
}.

#[export]
#[refine]
Instance Birelator_prod : Birelator prod :=
{
  birelate := fun A B RA RB '(a1, b1) '(a2, b2) => RA a1 a2 /\ RB b1 b2;
}.
Proof.
  intros A B p1 p2; split.
  - now destruct p1, p2; cbn; intros [-> ->].
  - now intros ->; destruct p2.
Defined.

(** Produkty i sumy są przykładami birelatorów. *)

#[export]
#[refine]
Instance Birelator_sum : Birelator sum :=
{
  birelate := fun A B RA RB x y =>
    match x, y with
    | inl a1, inl a2 => RA a1 a2
    | inr b1, inr b2 => RB b1 b2
    | _     , _      => False
    end;
}.
Proof.
  intros A B [a1 | b1] [a2 | b2]; cbn; [| easy.. |].
  - now split; congruence.
  - now split; congruence.
Defined.

(** * Relacje homogeniczne (TODO) *)

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

(** * Relacje równoważności (TODO) *)

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
Fixpoint lookup (p : nat * nat) (l : list (nat * nat)) : bool :=
match l with
| [] => false
| (h1, h2) :: t =>
  if andb (Nat.eqb (fst p) h1) (Nat.eqb (snd p) h2)
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

(** * Relacje porządku (TODO) *)

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

(** * Relacje różności (TODO) *)

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

(** * Ostre porządki (TODO) *)

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

(** * Domknięcia (TODO) *)

Require Import Classes.RelationClasses.

(** ** Ogólne pojęcie domknięcia *)

(** Uwaga, najnowszy pomysł: przedstawić domknięcia w taki sposób, żeby
    niepostrzeżenie przywyczajały do monad. *)

Class Closure
  {A : Type}
  (Cl : rel A -> rel A) : Prop :=
{
  pres :
    forall R S : rel A,
      (R --> S) -> Cl R --> Cl S;
  step :
    forall R : rel A,
      forall x y : A, R x y -> Cl R x y;
  join :
    forall R : rel A,
      Cl (Cl R) --> Cl R;
}.

(** ** Domknięcie zwrotne *)

Inductive rc {A : Type} (R : rel A) : rel A :=
| rc_step : forall x y : A, R x y -> rc R x y
| rc_refl : forall x : A, rc R x x.

(* begin hide *)
#[global] Hint Constructors rc : core.

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

#[refine]
#[export]
Instance Closure_sc {A : Type} : Closure (@sc A) :=
{
  step := sc_step;
}.
(* begin hide *)
Proof.
  - induction 2.
    + constructor. apply H. assumption.
    + constructor 2. apply H. assumption.
  - inversion 1; subst.
    + assumption.
    + destruct H0.
      * now constructor 2.
      * now constructor.
Qed.
(* end hide *)

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

(** ** Domknięcie zwrotnosymetryczne *)

Definition rsc {A : Type} (R : rel A) : rel A :=
  rc (sc' R).

(* begin hide *)
Ltac rsc := compute; repeat split; intros; rel;
repeat match goal with
| H : rc _ _ _ |- _ => induction H; eauto
| H : sc' _ _ _ |- _ => induction H; eauto
end; rel.
(* end hide *)

#[export]
Instance Reflexive_rsc :
  forall (A : Type) (R : rel A), Reflexive (rsc R).
(* begin hide *)
Proof. rsc. Qed.
(* end hide *)

#[export]
Instance Symmetric_rsc :
  forall (A : Type) (R : rel A), Symmetric (rsc R).
(* begin hide *)
Proof. rsc. Qed.
(* end hide *)

Lemma subrelation_rsc :
  forall (A : Type) (R : rel A), subrelation R (rsc R).
(* begin hide *)
Proof. rsc. Qed.
(* end hide *)

Lemma rsc_smallest :
  forall (A : Type) (R S : rel A),
    subrelation R S -> Reflexive S -> Symmetric S ->
      subrelation (rsc R) S.
(* begin hide *)
Proof. rsc. Qed.
(* end hide *)

Lemma rsc_idempotent :
  forall (A : Type) (R : rel A),
    rsc (rsc R) <--> rsc R.
(* begin hide *)
Proof. rsc. Qed.
(* end hide *)

Lemma rsc_Rinv :
  forall (A : Type) (R : rel A),
    Rinv (rsc (Rinv R)) <--> rsc R.
(* begin hide *)
Proof. rsc. Qed.
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
  R x y /\ forall z : A, rr R x z -> rr R z y -> False.

(*
#[export]
Instance Antitransitive_TransitiveReduction'
  {A : Type} (R : rel A)
  : Antitransitive (TransitiveReduction' R).
(* begin hide *)
Proof.
  compute. intros x y z [H11 H12] [H21 H22] [H31 H32].
Abort.
(* end hide *)
*)

(** ** Redukacja zwrotno-przechodnia *)

Definition ReflexiveTransitiveReduction {A : Type} (R : rel A) (x y : A) : Prop :=
  R x y /\ forall z : A, R x z -> R z y -> False.

(*
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
*)

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