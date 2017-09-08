
    Sedno naszego bólu wynika z postaci reguł indukcyjnych dla [even] oraz
    [odd]: mimo, że są to predykaty wzajemnie induktywne, Coq wygenerował
    dla nas reguły [even_ind] oraz [odd_ind], które nie tylko nie odwołują
    się do siebie nawzajem, ale w ogóle nie ma w nich żadnej indukcji.

    Na tym etapie naszej drogi do oświecenia remedium powinno być oczywiste:
    potrzebujemy dwóch wzajemnych reguł indukcyjnych. Na szczęście ich
    zdobycie nie będzie trudne: Coq potrafi je dla nas wygenerować. *)

Scheme even_mut_ind := Minimality for even Sort Prop
with odd_mut_ind := Minimality for odd Sort Prop.

(** Powyższa komenda mówi Coqowi mniej więcej tyle: wygeneruj dwie wzajemnie
    induktywne (minimalne) reguły eliminacji o nazwach [even_mut_ind] oraz
    [odd_mut_ind].

    Nie będziemy na razie rozwodzić się nad znaczeniem w tym kontekście słowa
    "minimalny". Przyjmij póki co na wiarę, że w przypadku induktywnych
    predykatów i relacji reguły minimalne są lepsze od innych.

    (Pewnie zastanawiasz się, dlaczego Coq domyślnie nie wygenerował reguł
    [even_mut_ind] oraz [odd_mut_ind], skoro to potrafi. Cóż, ja też się
    nad tym zastanawiam...)

    (W tym miejscu nasuwa mi się pewien żart programistyczny: Scheme to nie
    język programowania, [Scheme] to komenda Coqa służąca do generowania
    reguł indukcyjnych.)

    Aby lepiej zrozumieć wygenerowane reguły, przyjrzyjmy się im. *)

Check even_mut_ind.
(* ===>
even_mut_ind
     : forall P P0 : nat -> Prop,
       P 0 ->
       (forall n : nat, odd n -> P0 n -> P (S n)) ->
       (forall n : nat, even n -> P n -> P0 (S n)) ->
       forall n : nat, even n -> P n *)

(** Mamy tutaj dwa predykaty [P, P : nat -> Prop]. Nie powinno nas to dziwić
    — przecież będziemy dowodzić dwóch twierdzeń na raz. Reszta reguły mówi,
    że aby udowodnić [forall n : nat, even n -> P n], wystarczy, że pokażemy,
    że spełnione są następujące warunki:
    - po pierwsze musimy pokazać, że zachodzi [P 0]
    - po drugie musimy pokazać, że dla wszystkich nieparzystych [n], jeżeli
      zachodzi [P0 n], to [P (S n)]. Zauważ, że w tym stwierdzeniu występuje
      zarówno [P], jak i [P0]
    - po trzecie musimy pokazać, że dla wszystkich parzystych [n], jeżeli
      zachodzi [P n], to zachodzi także [P0 (S n)] *)

(** Reguła ta jest wybitnie podobna do zwykłek indukcji dla typu [nat]. Tam
    wyglądała ona mniej więcej tak: *)

(** [P 0] ~> [P 1] ~> [P 2] ~> ..., *)

(** gdzie symbol "~>" ma jedynie wizualnie przypominać strzałkę i nie ma nic
    wspólnego z implikacją czy funkcjami.

    Tym razem jest podobnie, ale mamy dwa różne predykaty [P] i [P0]. Wobec
    tego [even_mut_ind] można zwizualizować tak (dla większej jasności przez
    chwilę będziemy pisać [Q] zamiast [P0]): *)

(** [P 0] ~> [Q 1] ~> [P 2] ~> [Q 3] ~> [P 4] ~> ... *)

(** Reguła [odd_mut_ind] jest analogiczna. Ba! Właściwie jedyną rzeczą, jaką
    różni się od [even_mut_ind], jest to, że w konkluzji ma [P0 n], podczas
    gdy [even_mut_ind] ma tam [P n].

    Skoro mamy już odpowiednią regułę indukcyjną, czas użyć jej do opuszczenia
    naszej matni. *)

Theorem even_plus :
  forall n m : nat, even n -> even m -> even (n + m).
Proof.
  intros n m H. generalize dependent m.
  induction H using even_mut_ind with
    (P0 := fun n : nat => forall m : nat, even m -> odd (n + m)); intros.
    simpl. assumption.
    simpl. constructor. apply IHeven. assumption.
    simpl. constructor. apply IHeven. assumption.
Qed.

(** W powyższym dowodzie najpierw wprowadzamy do kontekstu [n], [m] i [H].
    Następnie używamy taktyki [generalize dependent], która jest odwrotnością
    [intro] — służy ona do przerzucania rzeczy z kontekstu do celu. Jeżeli
    [intro m] odczytamy jako "weźmy dowolne [m]", to [generalize dependent m]
    możemy odczytać: "zamiast naszego celu [G] dla tego konkretnego [m],
    udowodnijmy cel [forall m, G]".

    Cała operacja służy temu, abyśmy uzyskali jak najogólniejszą hipotezę
    indukcyjną — w szczególności chcemy, aby nasza hiptoeza indukcyjna
    była kwantyfikowana po [m] (więcej o generalizowaniu hipotezy indukcyjnej
    napiszę w przyszłości). Po tej operacji nasz cel zyskuje postać
    [forall m : nat, even m -> even (n + m)].

    Następnie musimy wykonać najtrudniejszy krok dowodu, czyli rozpocząć
    indukcję. Dotychczas było to proste — np. dla [n : nat] pisaliśmy po
    prostu [induction n] i wszystko się udawało. Nie zawsze jednak jest
    tak kolorowo.

    Przede wszystkim musimy wskazać regułe indukcyjną, której chcemy użyć
    do przeprowadzenia naszej indukcji — jeżeli tego nie zrobimy, użyta
    zostanie reguła domyślna, o której już wiemy, że nie zadziała. Po to
    właśnie jest klauzula [using even_mut_ind].

    Druga sprawa to wskazanie, czego tak właściwie będziemy przez indukcję
    dowodzić. Dotychczas było to banalne — nic nie pisaliśmy, a Coq sam
    potrafił wywnioskować postać tego zdania z celu. Tym razem jest jednak
    inaczej: chcemy dowodzić dwóch zdań na raz, ale z celu można wywnioskować
    tylko jedno.

    Zanim przejdziesz dalej — przyjrzyj się jeszcze raz postaci reguły
    [even_mut_ind].

    Użyta przez nas postać taktyki [induction] jest równoważna następującej
    (TODO: przepraszam za formatowanie, chwilowo nie umiem tego ładniej
    napisać): *)

(** [induction H using even_mut_ind with] *)

(** [(P := fun n : nat => forall m : nat, even m -> even (n + m)) *)

(** [(P0 := fun n : nat => forall m : nat, even m -> odd (n + m))] *)

(** Argumenty [P] i [P0] to zdania, których będziemy jednocześnie dowodzić.
    Argumentu [P] nie musieliśmy pisać, gdyż wynika on wprost z celu, który
    mamy udowodnić w chwili użycia taktyki [induction]. Jednak argumentu [P0]
    Coq nie jest w stanie sam wywnioskować. To, jaki ma on być, jest sprawą
    nietrywialną i zależy w pełni od nas — od naszego doświadczenia i wprawy
    w stosowaniu indukcji wzajemnej.

    Indukcja generuje nam 3 podcele, która odpowiadają następującym
    argumentom reguły indukcyjnej:
    - [P 0]
    - [forall n : nat, odd n -> P0 n -> P (S n)]
    - [forall n : nat, even n -> P n -> P0 (S n)] *)
       
(** Reszta dowodu przebiega w taki sposób, w jaki próbowaliśmy dowodzić
    wcześniej. Tym razem jednak skutkuje, gdyż dzięki nowej wzajemnej
    regule indukcyjnej dysponujemy wszystkimi potrzebnymi hipotezami
    indukcyjnymi. *)

(** **** Ćwiczenie *)

(** Udowodnij twierdzenia. Zanim to zrobisz, zastanów się: w których
    przypadkach potrzebna będzie indukcja wzajemna? *)

Theorem even_or_odd :
  forall n : nat, even n \/ odd n.
(* begin hide *)
Proof.
  induction n as [| n'].
    left. constructor.
    destruct IHn'; [right | left]; constructor; assumption.
Qed.
(* end hide *)

Theorem even_mult :
  forall n m : nat, even n -> even (n * m).
(* begin hide *)
Proof.
  induction m as [| m']; rewrite mult_comm; simpl; intros.
    constructor.
    apply even_plus.
      assumption.
      rewrite mult_comm. auto.
Qed.
(* end hide *)

Theorem even_double :
  forall n : nat, even (2 * n).
(* begin hide *)
Proof.
  induction n as [| n']; simpl in *.
    constructor.
    rewrite <- plus_n_O, plus_comm in *. simpl. do 2 constructor. assumption.
Qed.
(* end hide *)

(** Ufff... Dowodzenie za pomocą indukcji wzajemnej wydaje się skomplikowane.
    Musimy wygenerować odpowiednie reguły dziwną komendą (jeżeli nie zostały
    wygenerowane wcześniej), zgeneralizować hipotezę indukcyjną, zgadnąć
    twierdzenie pomocnicze i zainstancjować argumenty taktyki [induction].
    Strasznie dużo roboty.

    Jeżeli przyjrzałeś się dokładnie wiadomości wypisanej przez Coqa po [Qed]
    w lemacie [even_plus], dostrzegłeś zapewne zanjomy napis: [even_plus] is
    defined. Niby wszystko gra, ale zaraz! Czy przypadkiem nie zapewniałem
    cię, że będziemy dowodzić dwóch twierdzeń na raz?

    Istotnie tak było. Co więc stało się z drugim twierdzeniem? Czy dowodziliśmy
    tylko jednego? *)
