(** * BC2c: Polimorfizm, funkcje wyższego rzędu i klasy typów [TODO] *)

(** * Parametryzowane enumeracje (TODO) *)

Module param.

Inductive I (A B : Type) : Type :=
| c0 : A -> I A B
| c1 : B -> I A B
| c2 : A -> B -> I A B.

Arguments c0 {A B} _.
Arguments c1 {A B} _.
Arguments c2 {A B} _ _.

(** Kolejną innowacją są parametry, których głównym zastosowaniem jest
    polimorfizm. Dzięki parametrom możemy za jednym zamachem (tylko bez
    skojarzeń z Islamem!) zdefiniować nieskończenie wiele typów, po jednym
    dla każdego parametru. *)

Definition I_case_nondep_type : Type :=
  forall (A B P : Type) (c0' : A -> P) (c1' : B -> P) (c2' : A -> B -> P),
    I A B -> P.

(** Typ rekursora jest oczywisty: jeżeli znajdziemy rzeczy o kształtach
    takich jak konstruktory [I] z [I] zastąpionym przez [P], to możemy
    zrobić funkcję [I -> P]. Jako, że parametry są zawsze takie samo,
    możemy skwantyfikować je na samym początku. *)

Definition I_case_nondep
  (A B P : Type) (c0' : A -> P) (c1' : B -> P) (c2' : A -> B -> P)
  (i : I A B) : P :=
match i with
| c0 a => c0' a
| c1 b => c1' b
| c2 a b => c2' a b
end.

(** Implementacja jest banalna. *)

Definition I_case_dep_type : Type :=
  forall (A B : Type) (P : I A B -> Type)
    (c0' : forall a : A, P (c0 a))
    (c1' : forall b : B, P (c1 b))
    (c2' : forall (a : A) (b : B), P (c2 a b)),
      forall i : I A B, P i.

(** A regułę indukcji uzyskujemy przez uzależnienie [P] od [I]. *)

Definition I_case_dep
  (A B : Type) (P : I A B -> Type)
  (c0' : forall a : A, P (c0 a))
  (c1' : forall b : B, P (c1 b))
  (c2' : forall (a : A) (b : B), P (c2 a b))
  (i : I A B) : P i :=
match i with
| c0 a => c0' a
| c1 b => c1' b
| c2 a b => c2' a b
end.

End param.

(** * Parametryzowane rekordy (TODO) *)

(** * Klasy (TODO) *)

(** Mechanizmem ułatwiającym życie jeszcze bardziej niż rekordy są klasy.
    Niech nie zmyli cię ta nazwa — nie mają one nic wspólnego z klasami
    znanymi z języków imperatywnych. Bliżej im raczej do interfejsów,
    od których są zresztą dużo silniejsze.

    W językach imperatywnych interfejs możemy zaimplementować zazwyczaj
    definiując nowy typ. W Coqu możemy uczynić typ instancją klasy w
    dowolnym miejscu — nawet jeżeli to nie my go zdefiniowaliśmy. Co
    więcej, instancjami klas mogą być nie tylko typy, ale dowolne termy.
    Klasy są w Coqu pełnoprawnym tworem — mogą mieć argumenty, zawierać
    inne klasy, być przekazywane jako argumenty do funkcji etc. Używa się
    ich zazwyczaj dwojako:
    - zamiast rekordów (zwiększa to nieco czytelność)
    - jako interfejsy *)

Class EqDec (A : Type) : Type :=
{
  eq_dec : A -> A -> bool;
  eq_dec_spec : forall x y : A, eq_dec x y = true <-> x = y
}.

(** Nie będziemy po raz trzeci powtarzać (kulawej) definicji liczb
    wymiernych — użycie do tego klas zamiast rekordów sprowadza się
    do zamienienia słowa kluczowego [Record] na [Class] w poprzedniej
    definicji.

    Przyjrzyjmmy się za to wykorzystaniu klasy w roli interfejsu.
    Argument [A : Type] po nazwie klasy mówi nam, że nasz interfejs
    będą mogły implementować typy. Dalej zapis [: Type] mówi nam, że
    nasza klasa jest typem — klasy, jako ulepszone rekordy, są typami
    induktywnymi z jednym konstruktorem.

    Nasza klasa ma dwa pola, które będzie musiał podać użytkownik chcący
    uczynić swój typ jej instancją: funkcję [eq_dec] oraz jej specyfikację,
    która mówi nam, że [eq_dec] zwraca [true] wtedy i tylko wtedy, gdy jej
    argumenty są równe.

    Wobec tego typy będące instancjami [EqDec] można interpretować jako
    typy, dla których równość elementów można sprawdzić za pomocą jakiegoś
    algorytmu. Nie wszystkie typy posiadają tę własność — problematyczne
    są szczególnie te, których elementy są w jakiś sposób "nieskończone". *)

#[refine]
#[export]
Instance EqDec_bool : EqDec bool :=
{
  eq_dec := fun b b' : bool =>
    match b, b' with
    | true, true => true
    | false, false => true
    | _, _ => false
    end
}.
Proof.
  destruct x, y; split; trivial; inversion 1.
Defined.

(** Instancje klas definiujemy przy pomocy słowa kluczowego [Instance].
    Jeżeli używamy klasy jako interfejsu, który implementować mogą typy,
    to zazwyczaj będziemy potrzebować tylko jednej instancji, więc jej
    nazwa będzie niemal identyczna jak jej typ (dzięki temu łatwo będzie
    ją zapamiętać).

    Po symbolu [:=] w nawiasach klamrowych definiujemy pola, które
    nie są dowodami. Całość, jako komenda, musi kończyć się kropką. Gdy
    klasa nie zawiera żadnych pól będących dowodami, definicja jest
    zakończona. W przeciwnym przypadku Coq przechodzi w tryb dowodzenia,
    w którym każdemu polu będącemu dowodem odpowiada jeden podcel. Po
    rozwiązaniu wszystkich podcelów instancja jest zdefiniowana.

    W naszym przypadku klasa ma dwa pola — funkcję i dowód na to, że
    funkcja spełnia specyfikację — więc w nawiasach klamrowych musimy
    podać jedynie funkcję. Zauważmy, że nie musimy koniecznie definiować
    jej właśnie w tym miejscu — możemy zrobić to wcześniej, np. za pomocą
    komendy [Definition] albo [Fixpoint], a tutaj odnieść się do niej
    używając jej nazwy. W przypadku bardziej skomplikowanych definicji
    jest to nawet lepsze wyjście, gdyż zyskujemy dzięki niemu kontrolę
    nad tym, w którym miejscu rozwinąć definicję, dzięki czemu kontekst
    i cel stają się czytelniejsze.

    Ponieważ nasza klasa ma pole, które jest dowodem, Coq przechodzi w tryb
    dowodzenia. Dowód, mimo iż wymaga rozpatrzenia ośmiu przypadków, mieści
    się w jednej linijce — widać tutaj moc automatyzacji. Prześledźmy, co
    się w nim dzieje.

    Najpierw rozbijamy wartości boolowskie [x] i [y]. Nie musimy wcześniej
    wprowadzać ich do kontekstu taktyką [intros], gdyż [destruct] sam potrafi
    to zrobić. W wyniku tego dostajemy cztere podcele. W każdym z nich
    taktyką [split] rozbijamy równoważność na dwie implikacje. Sześć z nich
    ma postać [P -> P], więc radzi sobie z nimi taktyka [trivial]. Dwie
    pozostałe mają przesłanki postaci [false = true] albo [true = false],
    które są sprzeczne na mocy omówionych wcześniej właściwości konstruktorów.
    Taktyką [inversion 1] wskazujemy, że pierwsza przesłanka implikacji
    zawiera taką właśnie sprzeczną równość termów zrobionych różnymi
    konstruktorami, a Coq załatwia za nas resztę.

    Jeżeli masz problem z odczytaniem tego dowodu, koniecznie przeczytaj
    ponownie fragment rozdziału pierwszego dotyczący kombinatorów taktyk.
    Jeżeli nie potrafisz wyobrazić sobie podcelów generowanych przez
    kolejne taktyki, zastąp chwilowo średniki kropkami, a jeżeli to nie
    pomaga, udowodnij całe twierdzenie bez automatyzacji.

    Dzięki takim ćwiczeniom prędzej czy później oswoisz się z tym sposobem
    dowodzenia, choć nie jest to sztuka prosta — czytanie cudzych dowodów
    jest równie trudne jak czytanie cudzych programów.

    Prawie nigdy zresztą nowopowstałe dowody nie są od razu zautomatyzowane
    aż w takim stopniu — najpierw są przeprowadzone w części lub w całości
    ręcznie. Automatyzacja jest wynikiem dostrzeżenia w dowodzie pewnych
    powtarzających się wzorców. Proces ten przypomina trochę
    refaktoryzację kodu — gdy dostrzeżemy powtarzające się fragmenty kodu,
    przenosimy je do osobnych procedur. Analogicznie, gdy dostrzegamy
    powtarzające się fragmenty dowodu, łączymy je kombinatorami taktyk
    lub piszemy własne, zupełnie nowe taktyki (temat pisania własnych
    taktyk poruszę prędzej czy później).

    Od teraz będę zakładał, że nie masz problemów ze zrozumieniem takich
    dowodów i kolejne przykładowe dowody będę pisał w bardziej zwratej
    formie.

    Zauważ, że definicję instancji kończymy komendą [Defined], a nie [Qed],
    jak to było w przypadku dowodów twierdzeń. Wynika to z faktu, że Coq
    inaczej traktuje specyfikacje i programy, a inaczej zdania i dowody.
    W przypadku dowodu liczy się sam fakt jego istnienia, a nie jego treść,
    więc komenda [Qed] każe Coqowi zapamiętać jedynie, że twierdzenie
    udowodniono, a zapomnieć, jak dokładnie wyglądał proofterm. W przypadku
    programów takie zachowanie jest niedopuszczalne, więc [Defined] każe
    Coqowi zapamiętać term ze wszystkimi szczegółami. Jeżeli nie wiesz,
    której z tych dwóch komend użyć, użyj [Defined]. *)

(** **** Ćwiczenie ([EqDec]) *)

(** Zdefiniuj instancje klasy [EqDec] dla typów [unit] oraz [nat]. *)

(* begin hide *)
#[refine]
#[export]
Instance EqDec_unit : EqDec unit :=
{
  eq_dec := fun _ _ => true
}.
Proof.
  destruct x, y; split; trivial.
Defined.

#[refine]
#[export]
Instance EqDec_nat : EqDec nat :=
{
  eq_dec := fix f (n m : nat) :=
    match n, m with
    | 0, 0 => true
    | S n', S m' => f n' m'
    | _, _ => false
    end
}.
Proof.
  induction x.
    destruct y; split; trivial; inversion 1.
    induction y.
      split; inversion 1.
      split; intro.
        f_equal. apply IHx. assumption.
        inversion H; subst. destruct (IHx y) as [IHx1 IHx2].
          apply IHx2. trivial.
Defined.
(* end hide *)

(** **** Ćwiczenie (równość funkcji) *)

(** Czy możliwe jest zdefiniowanie instancji klasy [EqDec] dla typu:
    - [bool -> bool]
    - [bool -> nat]
    - [nat -> bool]
    - [nat -> nat]
    - [Prop] *)

(** Jeżeli tak, udowodnij w Coqu. Jeżeli nie, zaargumentuj słownie. *)

(* begin hide *)
(** Odpowiedzi:
    - Tak
    - Tak
    - Nie
    - Nie
    - Nie *)
(* end hide *)

#[refine]
#[export]
Instance EqDec_option (A : Type) (_ : EqDec A) : EqDec (option A) :=
{
  eq_dec := fun opt1 opt2 : option A =>
    match opt1, opt2 with
    | Some a, Some a' => eq_dec a a'
    | None, None => true
    | _, _ => false
    end
}.
Proof.
  destruct x, y; split; trivial; try (inversion 1; fail); intro.
    apply (eq_dec_spec a a0) in H. subst. trivial.
    apply (eq_dec_spec a a0). inversion H. trivial.
Defined.

(** Instancje klas mogą przyjmować argumenty, w tym również instancje innych
    klas albo inne instancje tej samej klasy. Dzięki temu możemy wyrazić
    ideę interfejsów warunkowych.

    W naszym przypadku typ [option A] może być instancją klasy [EqDec]
    jedynie pod warunkiem, że jego argument również jest instancją tej
    klasy. Jest to konieczne, gdyż porównywanie termów typu [option A]
    sprowadza się do porównywania termów typu [A].

    Zauważ, że kod [eq_dec a a'] nie odwołuje się do definiowanej właśnie
    funkcji [eq_dec] dla typu [option A] — odnosi się do funkcji [eq_dec],
    której dostarcza nam instancja [_ : EqDec A]. Jak widać, nie musimy
    nawet nadawać jej nazwy — Coqa interesuje tylko jej obecność.

    Na podstawie typów termów [a] i [a'], które są Coqowi znane, potrafi
    on wywnioskować, że [eq_dec a a'] nie jest wywołaniem rekurencyjnym,
    lecz odnosi się do instancji innej niż obecnie definiowana. Coq może
    ją znaleźć i odnosić się do niej, mimo że my nie możemy (gdybyśmy
    chcieli odnosić się do tej instancji, musielibyśmy zmienić nazwę z
    [_] na coś innego). *)

(** **** Ćwiczenie (równość list) *)

(** Zdefiniuj instancję klasy [EqDec] dla typu [list A]. *)

(* begin hide *)
Fixpoint eq_dec_list {A : Type} {eq_dec_A : EqDec A} (l l' : list A)
    : bool :=
match l, l' with
| nil, nil => true
| cons h t, cons h' t' => andb (eq_dec h h') (eq_dec_list t t')
| _, _ => false
end.

Require Import Bool.

#[refine]
#[export]
Instance EqDec_list (A : Type) (eq_dec_A : EqDec A) : EqDec (list A) :=
{
  eq_dec := eq_dec_list
}.
Proof.
  induction x as [| h t].
    destruct y; split; trivial; inversion 1.
    split.
      induction y as [| h' t']; cbn.
        inversion 1.
        intro. destruct eq_dec_A. apply andb_prop in H. destruct H.
          destruct (eq_dec_spec0 h h'), (IHt t').
            rewrite (H1 H), (H3 H0). reflexivity.
      intros ->. induction y as [| h' t']; cbn.
        reflexivity.
        rewrite IHt'. case_eq (eq_dec h' h'); intro.
          reflexivity.
          destruct eq_dec_A; cbn in *. destruct (eq_dec_spec0 h' h').
            rewrite <- H, H1; reflexivity.
Qed.
(* end hide *)

(** **** Ćwiczenie (równość funkcji 2) *)

(** Niech [A] i [B] będą dowolnymi typami. Zastanów się, kiedy możliwe
    jest zdefiniowanie instancji klasy [EqDec] dla [A -> B]. *)