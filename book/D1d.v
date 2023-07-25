(** * D1d: Indukcja wzajemna *)

Require Import Arith.

From Typonomikon Require Import D1c.

(** * Indukcja wzajemna *)

(** Jest jeszcze jeden rodzaj indukcji, o którym dotychczas nie mówiliśmy:
    indukcja wzajemna (ang. mutual induction). Bez zbędnego teoretyzowania
    zbadajmy sprawę na przykładzie klasyków polskiej literatury: *)

(** _Smok to wysuszony zmok_ *)

(** _Zmok to zmoczony smok_ *)

(** Stanisław Lem *)

(** Idea stojąca za indukcją wzajemną jest prosta: chcemy przez indukcję
    zdefiniować jednocześnie dwa obiekty, które mogą się nawzajem do siebie
    odwoływać.

    W owym definiowaniu nie mamy rzecz jasna pełnej swobody — obowiązują te
    same kryteria co w przypadku zwykłych, "pojedynczych" definicji typów
    induktywnych. Wobec tego zauważyć należy, że definicja słowa "smok"
    podana przez Lema jest według Coqowych standardów nieakceptowalna, gdyż
    jeżeli w definicji _smoka_ rozwiniemy definicję _zmoka_, to otrzymamy

    _Smok to wysuszony zmoczony smok_ *)

(** Widać gołym okiem, iż próba zredukowania (czyli obliczenia) obiektu
    _smok_ nigdy się nie skończy. Jak już wiemy, niekończące się obliczenia
    w logice odpowiadają sprzeczności, a zatem ani _smoki_, ani _zmoki_ w
    Coqowym świecie nie istnieją.

    Nie znaczy to bynajmniej, że wszystkie definicje przez indukcję
    wzajemną są w Coqu niepoprawne, choć należy przyznać, że są dość
    rzadko używane. Czas jednak abyśmy ujrzeli pierwszy prawdziwy przkład
    indukcji wzajemnej. *)

Module MutInd.

Inductive even : nat -> Prop :=
| even0 : even 0
| evenS : forall n : nat, odd n -> even (S n)

with odd : nat -> Prop :=
| oddS : forall n : nat, even n -> odd (S n).

(** Aby zrozumieć tę definicję, zestawmy ją z naszą definicją parzystości
    z sekcji _Induktywne predykaty_.

    Zdefiniowaliśmy tam predykat bycia liczbą parzystą tak:
    - [0] jest parzyste
    - jeżeli [n] jest parzyste, to [n + 2] też jest parzyste *)

(** Tym razem jednak nie definiujemy jedynie predykatu "jest liczbą parzystą".
    Definiujemy jednocześnie dwa predykaty: "jest liczbą parzystą" oraz
    "jest liczbą nieparzystą", które odwołują się do siebi nawzajm. Definicja
    brzmi tak:
    - [0] jest parzyste
    - jeżeli [n] jest nieparzyste, to [n + 1] jest parzyste
    - jeżeli [n] jest parzyste, to [n + 1] jest nieparzyste *)

(** Czy definicja taka rzeczywiście ma sens? Sprawdźmy to:
    - [0] jest parzyste na mocy definicji
    - jeżeli [0] jest parzyste (a jest), to [1] jest nieparzyste
    - jeżeli [1] jest nieparzyste (a jest), to [2] jest parzyste
    - i tak dalej, ad infinitum
*)

(** Jak widać, za pomocą naszej wzajemnie induktywnej definicji [even] można
    wygenerować wszystkie liczby parzyste (i tylko je), tak więc nowe [even]
    jest równoważne staremu [even] z sekcji _Induktywne predykaty_. Podobnie
    [odd] może wygenerować wszystkie liczby nieparzyste i tylko je. *)

(** **** Ćwiczenie (upewniające) *)

(** Upewnij się, że powyższy akapit nie kłamie. *)

Lemma even_0 : even 0.
(* begin hide *)
Proof. constructor. Qed.
(* end hide *)

Lemma odd_1 : odd 1.
(* begin hide *)
Proof. repeat constructor. Qed.
(* end hide *)

Lemma even_2 : even 2.
(* begin hide *)
Proof. repeat constructor. Qed.
(* end hide *)

Lemma even_42 : even 42.
(* begin hide *)
Proof. repeat constructor. Qed.
(* end hide *)

Lemma not_odd_0 : ~ odd 0.
(* begin hide *)
Proof. inversion 1. Qed.
(* end hide *)

Lemma not_even_1 : ~ even 1.
(* begin hide *)
Proof. inversion 1. inversion H1. Qed.
(* end hide *)

(** **** Ćwiczenie (właściwości [even] i [odd]) *)

(** Udowodnij podstawowe właściwości [even] i [odd]. *)

Lemma even_SS :
  forall n : nat, even n -> even (S (S n)).
(* begin hide *)
Proof.
  induction n; intro; do 2 constructor.
    constructor.
    assumption.
Qed.
(* end hide *)

Lemma odd_SS : 
  forall n : nat, odd n -> odd (S (S n)).
(* begin hide *)
Proof.
  induction n; intro; do 2 constructor; auto.
Qed.
(* end hide *)

Lemma even_plus :
  forall n m : nat, even n -> even m -> even (n + m).
(* begin hide *)
Abort.
(* end hide *)

(** Jeśli poległeś przy ostatnim zadaniu — nie przejmuj się. Specjalnie
    dobrałem złośliwy przykład.

    W tym momencie należy sobie zadać pytanie: jak dowodzić właściwości
    typów wzajemnie induktywnych? Aby udzielić odpowiedzi, spróbujmy
    udowodnić [even_plus] za pomocą indukcji po [n], a potem prześledźmy,
    co poszło nie tak. *)

Lemma even_plus_failed_1 : 
  forall n m : nat, even n -> even m -> even (n + m).
Proof.
  induction n; intros.
    assumption.
    cbn. constructor. inversion H; subst.
Abort.

(** Nasza indukcja po [n] zawiodła, gdyż nasza hipoteza indukcyjna ma w
    konkluzji [even (n + m)], podczas gdy nasz cel jest postaci
    [odd (n + m)]. Zauważmy, że teoretycznie cel powinno dać się udowodnić,
    jako że mamy hipotezy [even m] oraz [odd n], a suma liczby parzystej i
    nieparzystej jest nieparzysta.

    Nie zrażajmy się jednak i spróbujmy indukcji po dowodzie [even n]. *)

Lemma even_plus_failed_2 : 
  forall n m : nat, even n -> even m -> even (n + m).
Proof.
  induction 1; cbn; intro.
    assumption.
    constructor.
Abort.

(** Nasza indukcja po dowodzie hipotezy [even n] zawiodła, i to z kretesem,
    gdyż w kontekście nie mamy nawet żadnej hipotezy indukcyjnej! Co właściwie
    się stało? *)

Check even_ind.
(* ===> even_ind :
     forall P : nat -> Prop,
     P 0 -> (forall n : nat, odd n -> P (S n)) ->
       forall n : nat, even n -> P n *)

(** Jak widać, w naszej hipotezie "indukcyjnej" wygenerowanej przez Coqa w
    ogóle nie ma żadnej indukcji. Jest tam jedynie odwołanie do predykatu
    [odd]...

    Zauważmy jednak, że naszym celem znów było [odd (n + m)], a hipotezy
    [odd n] oraz [even m] sprawiają, że w teorii powinno dać się ten cel
    udowodnić, gdyż suma liczby parzystej i nieparzystej jest nieparzysta.

    Mogłoby się zdawać, że cierpimy na niedopasowanie (próba 1) lub brak
    (próba 2) hipotez indukcyjnych. Wydaje się też, że skoro w obydwu
    próbach zatrzymaliśmy się na celu [odd (n + m)], to pomocne mogłoby
    okazać się poniższe twierdzenie. *)

Lemma odd_even_plus_failed :
  forall n m : nat, odd n -> even m -> odd (n + m).
Proof.
  induction n; intros.
    inversion H.
    cbn. constructor. inversion H; subst.
Abort.

(** Niestety — nie dla psa kiełbasa, gdyż natykamy się na problemy bliźniaczo
    podobne do tych, które napotkaliśmy w poprzednim twierdzeniu: nasza
    hipoteza indukcyjna ma w konkluzji [odd (n + m)], podczas gdy nasz cel
    jest postaci [even (n + m)].

    Próba przepchnięcia lematu za pomocą indukcji po dowodzie hipotezy
    [odd n] także nie zadziała, z tych samych powodów dla których indukcja
    po [even n] nie pozwoliła nam udowodnić [even_plus]. Zauważmy jednak, że
    cel jest udowadnialny, gdyż jako hipotezy mamy [even n] oraz [even m],
    a suma dwóch liczb parzystych jest parzysta.

    Wydaje się, że wpadliśmy w błędne koło i jesteśmy w matni, bez wyjścia,
    bez nadziei, bez krzty szans na powodzenie: w dowodzie [even_plus]
    potrzebujemy lematu [odd_even_plus], ale nie możemy go udowodnić, gdyż
    w dowodzie [odd_even_plus] wymagane jest użycie lematu [even_plus].
    Ehhh, gdybyśmy tak mogli udowodnić oba te twierdzenia na raz...

    Eureka!

    Zauważ, że w naszych dotychczasowych dowodach przez indukcję posługiwaliśmy
    się zwykłą, "pojedynczą" indukcją. Była ona wystarczająca, gdyż mieliśmy do
    czynienia jedynie ze zwykłymi typami induktywnymi. Tym razem jednak jest
    inaczej: w ostatnich trzech dowodach chcieliśmy użyć "pojedynczej" indukcji
    do udowodnienia czegoś na temat predykatów wzajemnie induktywnych.

    Jest to ogromny zgrzyt. Do dowodzenia właściwości typów wzajemnie
    induktywnych powinniśmy użyć... o zgrozo, jak mogliśmy to przeoczyć,
    przecież to takie oczywiste... indukcji wzajemnej!

    Najprostszy sposób przeprowadzenia tego dowodu wygląda tak: *)

Lemma even_plus :
  forall n m : nat, even n -> even m -> even (n + m)
with odd_even_plus :
  forall n m : nat, odd n -> even m -> odd (n + m).
Proof.
  assumption.
  assumption.
Fail Qed.
Restart.
  destruct n as [| n']; cbn; intros.
    assumption.
    constructor. apply odd_even_plus.
      inversion H. assumption.
      assumption.
  destruct n as [| n']; cbn; intros.
    inversion H.
    constructor. apply even_plus.
      inversion H. assumption.
      assumption.
Qed.

(** Co tu się właściwie stało? Pierwsze dwie linijki są takie same jak
    poprzednio: stwierdzamy, że będziemy dowodzić twierdzenia o podanej
    nazwie i postaci. Następnie mamy słowo kluczowe [with], które pełni
    tu rolę podobną jak w definicjach przez indukcję wzajemną: podając po
    nim nazwę i postać twierdzenia mówimy Coqowi, że chcemy dowodzić tego
    twierdzenia ([odd_even_plus]) jednocześnie z poprzednim ([even_plus]).

    Dotychczas po rozpoczęciu dowodu ukazywał nam się jeden cel. Tym razem,
    jako że dowodzimy dwóch twierdzeń jednocześnie, mamy przed sobą dwa cele.
    W kontekście mamy też od razu dwie hipotezy indukcyjne. Musimy na nie
    bardzo uważać: dotychczas hipotezy indukcyjne pojawiały się dopiero w
    kroku indukcyjnym i sposób ich użycia był oczywisty. Tym razem jest
    inaczej — jako, że mamy je od samego początku, możemy natychmiast użyć
    ich do "udowodnienia" naszych twierdzeń.

    Niestety, takie "udowodnienie" odpowiada wywołaniu rekurencyjnemu na
    argumencie, który nie jest strukturalnie mniejszy (coś jak [f x := f x]).
    Fakt ten obrazuje wiadomość o błędzie, jaką Coq daje nam po tej próbie: *)

(* ===> Error: Cannot guess decreasing argument of fix. *)

(** Zaczynamy dowód od nowa, tym razem już bez oszukiwania. Musimy udowodnić
    każdy z naszych celów osobno, ale możemy korzystać z obydwu hipotez
    indukcyjnych. W obydwu celach zaczynamy od analizy przypadków, czyli
    rozbicia [n], i rozwiązania przypadku bazowego. Rozbicie [n] dało nam
    [n'], które jest strukturalnie mniejsze od [n], a zatem możemy bez obaw
    użyć naszej hipotezy indukcyjnej. Reszta jest trywialna. *)

Lemma even_double :
  forall n : nat, even (2 * n).
Proof.
  induction n as [| n']; cbn in *; constructor.
  rewrite <- plus_n_O in *. rewrite Nat.add_comm. cbn. constructor.
    assumption.
Qed.

End MutInd.

(** * Reguły indukcji dla typów wzajemnych (TODO) *)

Module mutual.

Unset Elimination Schemes.

Inductive Smok : Type :=
| Wysuszony : Zmok -> Smok

with Zmok : Type :=
| Zmoczony : Smok -> Zmok.

(** Indukcja wzajemna pozwala definiować na raz wiele typów, które mogą
    odwoływać się do siebie nawzajem. Cytując klasyków: smok to wysuszony
    zmok, zmok to zmoczony smok. *)

Definition Smok_case_nondep_type : Type :=
  forall S : Type, (Zmok -> S) -> Smok -> S.

Definition Zmok_case_nondep_type : Type :=
  forall Z : Type, (Smok -> Z) -> Zmok -> Z.

(** Reguła niezależnej analizy przypadków dla [Smok]a wygląda banalnie:
    jeżeli ze [Zmok]a potrafimy wyprodukować [S], to ze [Smok]a też.
    Dla [Zmok]a jest analogicznie. *)

Definition Smok_case_nondep
  (S : Type) (Wy : Zmok -> S) (smok : Smok) : S :=
match smok with
| Wysuszony zmok => Wy zmok
end.

Definition Zmok_case_nondep
  (Z : Type) (Zm : Smok -> Z) (zmok : Zmok) : Z :=
match zmok with
| Zmoczony smok => Zm smok
end.

(** Implementacja jest banalna. *)

Definition Smok_rec_type : Type :=
  forall S Z : Type, (Z -> S) -> (S -> Z) -> Smok -> S.

Definition Zmok_rec_type : Type :=
  forall S Z : Type, (Z -> S) -> (S -> Z) -> Zmok -> Z.

(** Typ rekursora jest jednak nieco bardziej zaawansowany. Żeby zdefiniować
    funkcję typu [Smok -> S], musimy mieć nie tylko rzeczy w kształcie
    konstruktorów [Smok]a, ale także w kształcie konstruktorów [Zmok]a,
    gdyż rekurencyjna struktura obu typów jest ze sobą nierozerwalnie
    związana. *)

Fixpoint Smok_rec
  (S Z : Type) (Wy : Z -> S) (Zm : S -> Z) (smok : Smok) : S :=
match smok with
| Wysuszony zmok => Wy (Zmok_rec S Z Wy Zm zmok)
end

with Zmok_rec
  (S Z : Type) (Wy : Z -> S) (Zm : S -> Z) (zmok : Zmok) : Z :=
match zmok with
| Zmoczony smok => Zm (Smok_rec S Z Wy Zm smok)
end.

(** Implementacja wymaga rekursji wzajemnej, ale poza nie jest jakoś
    wybitnie groźna. *)

Definition Smok_ind_type : Type :=
  forall (S : Smok -> Type) (Z : Zmok -> Type)
    (Wy : forall zmok : Zmok, Z zmok -> S (Wysuszony zmok))
    (Zm : forall smok : Smok, S smok -> Z (Zmoczony smok)),
      forall smok : Smok, S smok.

Definition Zmok_ind_type : Type :=
  forall (S : Smok -> Type) (Z : Zmok -> Type)
    (Wy : forall zmok : Zmok, Z zmok -> S (Wysuszony zmok))
    (Zm : forall smok : Smok, S smok -> Z (Zmoczony smok)),
      forall zmok : Zmok, Z zmok.

Fixpoint Smok_ind
  (S : Smok -> Type) (Z : Zmok -> Type)
  (Wy : forall zmok : Zmok, Z zmok -> S (Wysuszony zmok))
  (Zm : forall smok : Smok, S smok -> Z (Zmoczony smok))
  (smok : Smok) : S smok :=
match smok with
| Wysuszony zmok => Wy zmok (Zmok_ind S Z Wy Zm zmok)
end

with Zmok_ind
  (S : Smok -> Type) (Z : Zmok -> Type)
  (Wy : forall zmok : Zmok, Z zmok -> S (Wysuszony zmok))
  (Zm : forall smok : Smok, S smok -> Z (Zmoczony smok))
  (zmok : Zmok) : Z zmok :=
match zmok with
| Zmoczony smok => Zm smok (Smok_ind S Z Wy Zm smok)
end.

(** Mając rekursor, napisanie typu reguły indukcji jest banalne, podobnie
    jak jego implementacja. *)

Fixpoint even (n : nat) : bool :=
match n with
| 0 => true
| S n' => odd n'
end

with odd (n : nat) : bool :=
match n with
| 0 => false
| S n' => even n'
end.

End mutual.