(** * D0: Enumeracje i rekordy *)

(** UWAGA: ten rozdział został naprędce posklejany z fragmentów innych,
    więc może nie mieć większego sensu. *)

(** * Enumeracje (TODO) *)

(* begin hide *)
(*
TODO 1: przykładowe typy: dni tygodnia, miesiące, pory roku, strony świata
TODO 2: opisać opcje za pomocą analogii do "która godzina", jak w
TODO 2: https://www.cs.cmu.edu/~15150/previous-semesters/2012-spring/resources/lectures/09.pdf
TODO 3: boole pozwalają patrzeć, opcje pozwalają widzieć
*)
(* end hide *)

(** * Enumeracje z argumentami (TODO) *)

(** * Parametryzowane enumeracje (TODO) *)

(** * Indeksowane enumeracje (TODO) *)

(* begin hide *)
(*
TODO: Maszyny stanowe i type-driven design jako ćwiczenia
TODO: do (indeksowanych) enumeracji.
*)
(* end hide *)

(** * Rekordy (TODO) *)

(** W wielu językach programowania występują typy rekordów (ang. record
    types). Charakteryzują się one tym, że mają z góry określoną ilość
    pól o potencjalnie różnych typach. W językach imperatywnych rekordy
    wyewoluowały zaś w obiekty, które różnią się od rekordów tym, że mogą
    zawierać również funkcje, których dziedziną jest obiekt, w którym
    funkcja się znajduje.

    W Coqu mamy do dyspozycji rekordy, ale nie obiekty. Trzeba tu po raz
    kolejny pochwalić siłę systemu typów Coqa — o ile w większości języków
    rekordy są osobnym konstruktem językowym, o tyle w Coqu mogą być one z
    łatwością reprezentowane przez typy induktywne z jednym konstruktorem
    (wraz z odpowiednimi projekcjami, które dekonstruują rekord). *)

Module rational2.

Record rational : Set :=
{
    sign : bool;
    numerator : nat;
    denominator : nat;
    denominator_not_zero : denominator <> 0
}.

(** Z typem induktywnym o jednym konstruktorze już się zetknęliśmy,
    próbując zdefiniować liczby wymierne. Powyższa definicja używająca
    rekordu ma drobną przewagę nad poprzednią, w której słowo kluczowe
    [Inductive] pada explicité:
    - wygląda ładniej
    - ma projekcje *)

Check sign.
(* ===> sign : rational -> bool *)

Check denominator_not_zero.
(* ===> denominator_not_zero
    : forall r : rational, denominator r <> 0 *)

(** Dzięki projekcjom mamy dostęp do poszczególnych pól rekordu bez
    konieczności jego dekonstruowania — nie musimy używać konstruktu
    [match] ani taktyki [destruct], jeżeli nie chcemy. Często bywa to
    bardzo wygodne.

    Projekcję [sign] możemy interpretować jako funkcję, która bierze
    liczbę wymierną [r] i zwraca jej znak, zaś projekcja
    [denominator_not_zero] mówi nam, że mianownik żadnej liczb wymiernej
    nie jest zerem.

    Pozwa tymi wizualno-praktycznymi drobnostkami, obie definicje są
    równoważne (w szczególności, powyższa definicja, podobnie jak
    poprzednia, nie jest dobrą reprezentacją liczb wymiernych). *)

End rational2.

(** **** Ćwiczenie (kalendarz) *)

(** Zdefiniuj typ induktywny reprezentujący datę i napisz ręcznie
    wszystkie projekcje. Następnie zdefiniuj rekord reprezentujący
    datę i zachwyć się tym, ile czasu i głupiego pisania zaoszczędziłbyś,
    gdybyś od razu użył rekordu... *)

(* begin hide *)
(* TODO : zrób to ćwiczenie *)
(* end hide *)

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

(** Instancje klas definiujemy przy pomocy słowa kluczowego [#[refine]
Instance].
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
Instance EqDec_unit : EqDec unit :=
{
    eq_dec := fun _ _ => true
}.
Proof.
  destruct x, y; split; trivial.
Defined.

#[refine]
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

Search (andb _ _ = true -> _).

#[refine]
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

(* begin hide *)

(* TODO: *)

(*
Set Primitive Projections.
*)

CoInductive wut : Type :=
{
    a : nat;
    b : bool;
}.

Print a.

Lemma wut' :
  forall x y : wut,
    a x = a y -> b x = b y -> x = y.
Proof.
  intros. destruct x, y. cbn in *. rewrite H, H0. reflexivity.
Qed.

Goal
  forall w : wut,
    w = {| a := a w; b := b w |}.
Proof.
  intro. destruct w. cbn. reflexivity. 
Qed.

(* end hide *)