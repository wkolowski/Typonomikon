(** * BC2a: Konstruktywny rachunek kwantyfikatorów [TODO] *)

From Typonomikon Require Export BC1b.

(** * Predykaty i relacje (TODO) *)

(** * Kwantyfikatory *)

(** Komenda [End] zamyka sekcję, którą otworzyliśmy na samym początku
    tego rozdziału. Zdania [P], [Q] i [R] znikają z
    dostępnej dla nas przestrzeni nazw, dzięki czemu uniknęliśmy jej
    zaśmiecenia. Nasze twierdzenia wciąż są jednak dostępne (sprawdź
    to).

    Zajmiemy się teraz konstruktywnym rachunkiem kwantyfikatorów. Jest on
    rozszerzeniem omówionego przed chwilą konstruktywnego rachunku zdań
    o kwantyfikatory, które pozwolą nam wyrażać takie zależności jak "każdy"
    oraz "istnieje", oraz o predykaty i relacje, które mózemy interpretować
    odpowiednio jako właściwości obiektów oraz zależności między obiektami. *)

(** ** Kwantyfikacja uniwersalna *)

(** Zobaczmy o co chodzi na znanym nam już przykładzie zwrotności
    implikacji: *)

Lemma impl_refl'' : forall P : Prop, P -> P.
Proof.
  intros. assumption.
Qed.

(** [forall] oznacza kwantyfikację uniwersalną. Możemy ten symbol
    odczytywać "dla każdego". Zasięg kwantyfikatora rozciąga się
    od przecinka aż do kropki. Wobec tego treść naszego twierdzenia
    możemy odczytać "dla każdego zdania logicznego P, P implikuje P".

    Kwantyfikator uniwersalny jest w swej naturze bardzo podobny do
    implikacji — zmienne, których dotyczy, możemy wprowadzić do
    kontekstu przy pomocy taktyki [intro]. W dowodzie nieforamlnym
    użyciu taktyki [intro P] na celu kwantyfikowanym uniwersalnie
    odpowiadałoby stwierdzenie "niech P będzie dowolnym zdaniem logicznym".

    Zauważ, że używając taktyki [intros], możemy wprowadzić do kontekstu
    jednocześnie zmienne kwantyfikowane uniwersalnie oraz przesłanki
    występujące po lewej stronie implikacji. To wszystko powinno nasunąć
    nam myśl, że kwantyfikacja uniwersalna i implikacja są ze sobą blisko
    związane. *)

Print impl_refl''.
(* ===> impl_refl'' = fun (P : Prop) (H : P) => H
          : forall P : Prop, P -> P *)

(** Rzeczywiście: dowodem naszego zdania jest coś, co na pierwszy rzut
    oka wygląda jak funkcja. Jeżeli jednak przyjrzysz się jej uważnie,
    dostrzeżesz że nie może być to zwykła funkcja — typ zwracanej
    wartości [H] różni się w zależności od argumentu [P]. Jeżeli
    za [P] wstawimy [1 = 1], to [H] będzie dowodem na to, że
    [1 = 1]. Jeżeli za [P] wstawimy [2 = 2], to [H] będzie dowodem
    na to, że [2 = 2]. Zauważ, że [1 = 1] oraz [2 = 2] to dwa różne
    zdania, a zatem są to także różne typy.

    Dowód naszego zdania nie może być zatem zwykłą funkcją — gdyby
    nią był, zawsze zwracałby wartości tego samego typu. Jest on
    funkcją zależną, czyli taką, której przeciwdziedzina zależy
    od dziedziny. Funkcja zależna dla każdego argumentu może
    zwracać wartości różnego typu.

    Ustaliliśmy więc, że kwantyfikacja uniwersalna jest pewnym
    uogólnieniem implikacji, zaś jej interpretacją obliczeniową
    jest funkcja zależna, czyli pewne uogólnienie zwykłej funkcji,
    która jest interpretacją obliczeniową implikacji. *)

Lemma general_to_particular :
  forall P : nat -> Prop,
    (forall n : nat, P n) -> P 42.
Proof.
  intros. apply H.
Restart.
  intros. specialize (H 42). assumption.
Qed.

(** Podobnie jak zwykłe funkcje, funkcje zależne możemy aplikować
    do celu za pomocą taktyki [apply]. Możliwy jest też inny
    sposób rozumowania, nieco bardziej przypominający rozumowania
    "w przód": przy pomocy taktyki [specialize] możemy zainstancjować
    [n] w naszej hipotezie [H], podając jej pewną liczbę naturalną.
    Wtedy nasza hipoteza [H] z ogólnej, z kwantyfikacją po wszystkich
    liczbach naturalnych, zmieni się w szczególną, dotyczącą tylko
    podanej przez nas liczby.

    Komenda [Restart] pozwala nam zacząć dowód od nowa w dowolnym
    jego momencie. Jej użycie nie jest wymagane, by ukończyć
    powyższy dowód — spróbuj wstawić w jej miejsce [Qed]. Użyłem jej
    tylko po to, żeby czytelnie zestawić ze sobą sposoby rozumowania
    w przód i w tył dla kwantyfikacji uniwersalnej. *)

Lemma and_proj1'' :
  forall (P Q : nat -> Prop),
    (forall n : nat, P n /\ Q n) -> (forall n : nat, P n).
Proof.
  intros P Q H k. destruct (H k). assumption.
Qed.

(** W powyższym przykładzie próba użycia taktyki [destruct] na
    hipotezie [H] zawiodłaby — [H] nie jest produktem. Żeby
    rozbić tę hipotezę, musielibyśmy najpierw wyspecjalizować
    ją dla interesującego nas [k], a dopiero potem rozbić.
    Możemy jednak zrobić to w nieco krótszy sposób — pisząc
    [destruct (H k)]. Dzięki temu "w locie" przemienimy [H]
    z hipotezy ogólnej w szczególną, dotycząca tylko [k], a
    potem rozbijemy. Podobnie poprzednie twierdzenie moglibyśmy
    udowodnić szybciej, jeżeli zamiast [specialize] i [assumption]
    napisalibyśmy [destruct (H 42)] (choć i tak najszybciej jest
    oczywiście użyć [apply H]. *)

(** **** Ćwiczenie (kwantyfikacja uniwersalna) *)

(** Udowodnij poniższe twierdzenie. Co ono oznacza? Przeczytaj je na głos.
    Zinterpretuj je, tzn. sparafrazuj. *)

Lemma all_dist :
  forall (A : Type) (P Q : A -> Prop),
    (forall x : A, P x /\ Q x) <->
    (forall x : A, P x) /\ (forall x : A, Q x).
(* begin hide *)
Proof.
  split.
    intros. split.
      intro. destruct (H x). assumption.
      intro. destruct (H x). assumption.
    intros. destruct H. split.
      apply H.
      apply H0.
Restart.
  split; intros.
    split; intros; destruct (H x); assumption.
    destruct H. split; try apply H; apply H0.
Qed.
(* end hide *)

(** ** Kwantyfikacja egzystencjalna *)

(** Zdania egzystencjalne to zdania postaci "istnieje obiekt x,
    który ma właściwość P". W Coqu prezentują się tak: *)

Lemma ex_example1 :
  exists n : nat, n = 0.
Proof.
  exists 0. trivial.
Qed.

(** Kwantyfikacja egzystencjalna jest w Coqu zapisywana jako [exists]
    (exists). Aby udowodnić zdanie kwantyfikowane egzystencjalnie, musimy
    skonstruować obiekt, którego istnienie postulujemy, oraz
    udowodnić, że ma deklarowaną właściwość. Jest to wymóg dużo
    bardziej restrykcyjny niż w logice klasycznej, gdzie możemy
    zadowolić się stwierdzeniem, że nieistnienie takiego obiektu
    jest sprzeczne.

    Powyższe twierdzenie możemy odczytać "istnieje liczba naturalna,
    która jest równa 0". W dowodzenie nieformalnym użyciu taktyki
    [exists] odpowiada stwierdzenie: "liczbą posiadającą tę właściwość
    jest 0". Następnie pozostaje nam udowodnić, iż rzeczywiście [0 = 0],
    co jest trywialne. *)

Lemma ex_example2 :
  ~ exists n : nat, 0 = S n.
Proof.
  intro. destruct H as [n H]. inversion H.
Qed.

(** Gdy zdanie kwantyfikowane egzystencjalnie znajdzie się w naszych
    założeniach, możemy je rozbić i uzyskać wspomniany w nim obiekt
    oraz dowód wspominianej właściwości. Nie powinno nas to dziwić —
    skoro zakładamy, że zdanie to jest prawdziwe, to musiało zostać
    ono udowodnione w sposób opisany powyżej — właśnie poprzez wskazanie
    obiektu i udowodnienia, że ma daną własność.

    Myślę, że dostrzegasz już pewną prawidłowość:
    - udowodnienie koniunkcji wymaga udowodnienia obydwu członów z osobna,
      więc dowód koniunkcji można rozbić na dowody poszczególnych członów
      (podobna sytuacja zachodzi w przypadku równoważności)
    - udowodnienie dysjunkcji wymaga udowodnienia któregoś z członów,
      więc dowód dysjunkcji można rozbić, uzyskując dwa osobne podcele,
      a w każdym z nich dowód jednego z członów tej dysjunkcji
    - udowodnienie zdania egzystencjalnego wymaga wskazania obiektu i
      podania dowodu żądanej własności, więc dowód takiego zdania
      możemy rozbić, uzyskując ten obiekt i dowód jego własności *)

(** Takie konstruowanie i dekonstruowanie dowodów (i innych termów)
    będzie naszym chlebem powszednim w logice konstruktywnej i w Coqu.
    Wynika ono z samej natury konstrukcji: zasady konstruowania termów
    danego typu są ściśle określone, więc możemy dokonywać dekonstrukcji,
    która polega po prostu na sprawdzeniu, jakimi zasadami posłużono się
    w konstrukcji. Nie przejmuj się, jeżeli wydaje ci się to nie do końca
    jasne — więcej dowiesz się już w kolejnym rozdziale.

    Ostatnią wartą omówienia sprawą jest interpretacja obliczeniowa
    kwantyfikacji egzystencjalnej. Jest nią para zależna, tzn. taka,
    w której typ drugiego elementu może zależeć od pierwszego — pierwszym
    elementem pary jest obiekt, a drugim dowód, że ma on pewną własność.
    Zauważ, że podstawiając [0] do [exists n : nat, n = 0], otrzymamy
    zdanie [0 = 0], które jest innym zdaniem, niż [1 = 0] (choćby dlatego,
    że pierwsze jest prawdziwe, a drugie nie). Interpretacją obliczeniową
    taktyki [exists] jest wobec tego podanie pierwszego elementu pary,
    a podanie drugiego to po prostu przeprowadzenie reszty dowodu.

    "Zależność" jest tutaj tego samego rodzaju, co w przypadku produktu
    zależnego — tam typ wyniku mógł być różny w zależność od wartości,
    jaką funkcja bierze na wejściu, a w przypadku sumy zależnej typ
    drugiego elementu może być różny w zależności od tego, jaki jest
    pierwszy element.

    Nie daj się zwieść niefortunnemu nazewnictwu: produkt zależny
    [forall x : A, B], którego elementami są funkcje zależne,
    jest uogólnieniem typu funkcyjnego [A -> B], którego elementami
    są zwykłe funkcje, zaś suma zależna [exists x : A, B], której
    elementami są pary zależne, jest uogólnieniem produktu [A * B],
    którego elementami są zwykłe pary. *)

(** **** Ćwiczenie (kwantyfikacja egzystencjalna) *)

(** Udowodnij poniższe twierdzenie. *)

Lemma ex_or_dist :
  forall (A : Type) (P Q : A -> Prop),
    (exists x : A, P x \/ Q x) <->
    (exists x : A, P x) \/ (exists x : A, Q x).
(* begin hide *)
Proof.
  split.
    intros. destruct H as [x [HP | HQ]].
      left. exists x. assumption.
      right. exists x. assumption.
    intros. destruct H as [[x HP] | [x HQ]].
      exists x. left. assumption.
      exists x. right. assumption.
Qed.
(* end hide *)

(** * Równość - najważniejsza relacja (TODO) *)

(** Dobrze byłoby zapoznać się z równością przed pierwszym jej użyciem
    w rozdziale o typach induktywnych. Być może coś więcej o równości
    (i jej alternatywnej definicji?).*)

(** ** Równość według Arystotelesa *)

(** ** Równość według Leibniza *)

(** ** α-konwersja i inne rodzaje równości *)

(* begin hide *)
(*
TODO 1: Opisać związki rodzajów równości ze składnią i semantyką
        (empiryczna obserwacja: studenci pierwszego roku nie są
        zbyt płynni w posługiwaniu się składnią abstrakcyjną).
TODO 2: Pomysł na jeszcze jeden podrozdział, semantyka vs składnia
TODO 3: Użyć nominalizmów do wytłumaczenia wiązania nazw zmiennych.
*)
(* end hide *)

(** #<a class='link'
        href='https://github.com/wkolowski/Typonomikon/blob/master/txt/ściągi/równość.md'>
    Ściąga z równości</a>#. *)

(** ** Równość induktywna *)

Module MyEq.

(** Czym jest równość? To pytanie stawiało sobie wielu filozofów,
    szczególnie politycznych, zaś wyjątkowo rzadko nad tą sprawą
    zastanawiali się sami bojownicy o równość, tak jakby wszystko
    dokładnie wiedzieli. Odpowiedź na nie jest jednym z największych
    osiągnięć matematyki w dziejach: równość to jeden z typów induktywnych,
    które możemy zdefiniować w Coqu. *)

Inductive eq {A : Type} (x : A) : A -> Prop :=
| eq_refl : eq x x.

(** Spróbujmy przeczytać tę definicję: dla danego typu [A] oraz termu
    [x] tego typu, [eq x] jest predykatem, który ma jeden konstruktor
    głoszący, że [eq x x] zachodzi. Choć definicja taka brzmi obco i
    dziwacznie, ma ona swoje uzasadnienie (które niestety poznamy
    dopiero w przyszłości). *)

Lemma eq_refl_trivial : eq 42 42.
Proof.
  apply eq_refl.
Qed.

(** Poznane przez nas dotychczas taktyki potrafiące udowadniać proste
    równości, jak [trivial] czy [reflexivity] działają w ten sposób,
    że po prostu aplikują na celu [eq_refl]. Nazwa [eq_refl] to skrót
    od ang. "reflexivity of equality", czyli "zwrotność równości" —
    jest to najważniejsza cecha równości, która oznacza, że każdy term
    jest równy samemu sobie. *)

Lemma eq_refl_nontrivial : eq (1 + 41) 42.
Proof.
  constructor.
Qed.

(** Mogłoby wydawać się, że zwrotność nie wystarcza do udowadniania
    "nietrywialnych" równości pokroju [1 + 41 = 42], jednak tak nie jest.
    Dlaczego [eq_refl] odnosi na tym celu sukces skoro [1 + 41] oraz [42]
    zdecydowanie różnią się postacią? Odpowiedź jest prosta: typ [eq] w
    rzeczywistości owija jedynie równość pierwotną, wbudowaną w samo jądro
    Coqa, którą jest konwertowalność. *)

Lemma eq_refl_alpha :
  forall A : Type, eq (fun x : A => x) (fun y : A => y).
Proof.
  intro. change (fun x : A => x) with (fun y : A => y).
  apply eq_refl.
Qed.

Lemma eq_refl_beta :
  forall m : nat, eq ((fun n : nat => n + n) m) (m + m).
Proof.
  intro. cbn. apply eq_refl.
Qed.

Definition ultimate_answer : nat := 42.

Lemma eq_refl_delta : eq ultimate_answer 42.
Proof.
  unfold ultimate_answer. apply eq_refl.
Qed.

Lemma eq_refl_iota :
  eq 42 (match 0 with | 0 => 42 | _ => 13 end).
Proof.
  cbn. apply eq_refl.
Qed.

Lemma eq_refl_zeta :
  let n := 42 in eq n 42.
Proof.
  reflexivity.
Qed.

(** Przypomnijmy, co już wiemy o redukcjach:
    - konwersja alfa pozwala nam zmienić nazwę zmiennej związanej w
      funkcji anonimowej nową, jeżeli ta nie jest jeszcze używana.
      W naszym przykładzie zamieniamy [x] w [fun x : A => x] na [y],
      otrzymując [fun y : A => y] — konwersja jest legalna. Jednak
      w funkcji [fun x y : nat => x + x] nie możemy użyć konwersji
      alfa, żeby zmienić nazwę [x] na [y], bo [y] jest już używana
      (tak nazywa się drugi argument).
    - Redukcja beta zastępuje argumentem każde wystąpienie zmiennej
      związanej w funkcji anonimowej. W naszym przypadku redukcja
      ta zamienia [(fun n : nat => n + n) m] na [m + m] — w miejsce
      [n] wstawiamy [m].
    - Redukcja delta odwija definicje. W naszym przypadku zdefiniowaliśmy,
      że [ultimate_answer] oznacza [42], więc redukcja delta w miejsce
      [ultimate_answer] wstawia [42].
    - Redukcja jota wykonuje dopasowanie do wzorca. W naszym przypadku [0]
      jest termem, który postać jest znana (został on skonstruowany
      konstruktorem [0]) i który pasuje do wzorca [| 0 => 42], a zatem
      redukcja jota zamienia całe wyrażenie od [match] aż do [end]
      na [42].
    - Redukcja zeta odwija lokalną definicję poczynioną za pomocą [let]a *)

(** Termy [x] i [y] są konwertowalne, gdy za pomocą serii konwersji alfa
    oraz redukcji beta, delta, jota i zeta oba redukują się do tego samego
    termu (który dzięki silnej normalizacji istnieje i jest w postaci
    kanonicznej).

    Uważny czytelnik zada sobie w tym momencie pytanie: skoro równość to
    konwertowalność, to jakim cudem równe są termy [0 + n] oraz [n + 0],
    gdzie [n] jest zmienną, które przecież nie są konwertowalne?

    Trzeba tutaj dokonać pewnego doprecyzowania. Termy [0 + n] i [n + 0] są
    konwertowalne dla każdego konkretnego [n], np. [0 + 42] i [42 + 0] są
    konwertowalne. Konwertowalne nie są natomiast, gdy [n] jest zmienną -
    jest tak dlatego, że nie możemy wykonać redukcji iota, bo nie wiemy, czy
    [n] jest zerem czy następnikiem.

    Odpowiedzią na pytanie są reguły eliminacji, głównie dla typów
    induktywnych. Reguły te mają konkluzje postaci [forall x : I, P x],
    więc w szczególności możemy użyć ich dla [P x := x = y] dla jakiegoś
    [y : A]. Dzięki nim przeprowadzaliśmy już wielokrotnie mniej więcej
    takie rozumowania: [n] jest wprawdzie nie wiadomo czym, ale przez
    indukcję może to być albo [0], albo [S n'], gdzie dla [n'] zachodzi
    odpowiednia hipoteza indukcyjna. *)

End MyEq.

(** * Kwantyfikator unikatowy (TODO) *)

Definition unique {A : Type} (P : A -> Prop) : Prop :=
  exists x : A, P x /\ forall y : A, P y -> x = y.

(** Poznawszy relację równości oraz kwantyfikatory uniwersalny i
    egzystencjalny, możemy zdefiniować inny bardzo ważny "kwantyfikator",
    a mianowicie kwantyfikator unikatowy, który głosi, że istnieje
    dokładnie jeden obiekt spełniający daną właściwość. *)

(** * Paradoksy autoreferencji (TODO) *)

(** ** Paradoks golibrody *)

(** Języki naturalne, jakimi ludzie posługują się w życiu codziennym
    (polski, angielski suahili, język indian Navajo) zawierają spory
    zestaw spójników oraz kwantyfikatorów ("i", "a", "oraz", "lub",
    "albo", "jeżeli ... to", "pod warunkiem, że ", "wtedy", i wiele
    innych).

    Należy z całą stanowczością zaznaczyć, że te spójniki i kwantyfikatory,
    a w szczególności ich intuicyjna interpretacja, znacznie różnią się
    od analogicznych spójników i kwantyfikatorów logicznych, które mieliśmy
    okazję poznać w tym rozdziale. Żeby to sobie uświadomić, zapoznamy się
    z pewnego rodzaju "paradoksem". *)

Lemma barbers_paradox :
  forall (man : Type) (barber : man)
    (shaves : man -> man -> Prop),
      (forall x : man, shaves barber x <-> ~ shaves x x) -> False.
(* begin hide *)
Proof.
  intros. destruct (H barber). apply H0.
    apply H1. intro. apply H0; assumption.
    apply H1. intro. apply H0; assumption.
Qed.
(* end hide *)

(** Twierdzenie to formułowane jest zazwyczaj tak: nie istnieje człowiek,
    który goli wszystkich tych (i tylko tych), którzy sami siebie nie golą.

    Ale cóż takiego znaczy to przedziwne zdanie? Czy matematyka dają nam
    magiczną, aprioryczną wiedzę o fryzjerach?

    Odczytajmy je poetycko. Wyobraźmy sobie pewne miasteczko. Typ [man]
    będzie reprezentował jego mieszkańców. Niech term [barber] typu [man]
    oznacza hipotetycznego golibrodę. Hipotetycznego, gdyż samo użycie
    jakiejś nazwy nie powoduje automatycznie, że nazywany obiekt istnieje
    (przykładów jest masa, np. jednorożce, sprawiedliwość społeczna).

    Mamy też relację [shaves]. Będziemy ją interpretować w ten sposób, że
    [shaves a b] zachodzi, gdy [a] goli brodę [b]. Nasza hipoteza
    [forall x : man, shaves barber x <-> ~ shaves x x] jest zawoalowanym
    sposobem podania następującej definicji: golibrodą nazwiemy te osoby,
    który golą wszystkie te i tylko te osoby, które same siebie nie golą.

    Póki co sytuacja rozwija się w całkiem niekontrowersyjny sposób. Żeby
    zburzyć tę sielankę, możemy zadać sobie następujące pytanie: czy
    golibroda rzeczywiście istnieje? Dziwne to pytanie, gdy na każdym
    rogu ulicy można spotkać fryzjera, ale nie dajmy się zwieść.

    W myśl rzymskich sentencji "quis custodiet ipsos custodes?" ("kto będzie
    pilnował strażników?") oraz "medice, cure te ipsum!" ("lekarzu, wylecz
    sam siebie!") możemy zadać dużo bardziej konkretne pytanie: kto goli
    brody golibrody? A idąc jeszcze krok dalej: czy golibroda goli sam siebie?

    Rozstrzygnięcie jest banalne i wynika wprost z definicji: jeśli golibroda
    ([barber]) to ten, kto goli ([shaves barber x]) wszystkich tych i tylko
    tych ([forall x : man]), którzy sami siebie nie golą ([~ shaves x x]), to
    podstawiając [barber] za [x] otrzymujemy sprzeczność: [shaves barber
    barber] zachodzi wtedy i tylko wtedy, gdy [~ shaves barber barber].

    Tak więc golibroda, zupełnie jak Święty Mikołaj, nie istnieje. Zdanie to
    nie ma jednak wiele wspólnego ze światem rzeczywistym: wynika ono jedynie
    z takiej a nie innej, przyjętej przez nas całkowicie arbitralnie definicji
    słowa "golibroda". Można to łatwo zobrazować, przeformułowywując powyższe
    twierdzenie z użyciem innych nazw: *)

Lemma barbers_paradox' :
  forall (A : Type) (x : A) (P : A -> A -> Prop),
    (forall y : A, P x y <-> ~ P y y) -> False.
(* begin hide *)
Proof.
  intros. destruct (H x). apply H0.
    apply H1. intro. apply H0; assumption.
    apply H1. intro. apply H0; assumption.
Qed.
(* end hide *)

(** Nieistnienie "golibrody" i pokrewny mu paradoks pytania "czy golibroda
    goli sam siebie?" jest konsekwencją wyłącznie formy powyższego zdania
    logicznego i nie mówi nic o rzeczywistoświatych golibrodach.

    Paradoksalność całego "paradoksu" bierze się z tego, że typom, zmiennym
    i relacjom specjalnie nadano takie nazwy, żeby zwykły człowiek bez
    głębszych dywagacji nad definicją słowa "golibroda" przjął, że golibroda
    istnieje. Robiąc tak, wpada w sidła pułapki zastawionej przez logika i
    zostaje trafiony paradoksalną konkluzją: golibroda nie istnieje. *)

(** * Logika pierwszego rzędu a logika wyższego rzędu (TODO) *)

(** ** Logika pierwszego rzędu *)

(** ** Logika drugiego rzędu *)

(** ** Logika wyższego rzędu *)

(** * Predykatywizm i kodowania impredykatywne (TODO) *)

(* begin hide *)
(* TODO: Tautologie na kodowaniach impredykatywnych jako ćwiczenia z funkcji anonimowych *)
(* end hide *)

Definition iand (P Q : Prop) : Prop :=
  forall C : Prop, (P -> Q -> C) -> C.

Definition ior (P Q : Prop) : Prop :=
  forall C : Prop, (P -> C) -> (Q -> C) -> C.

Definition iTrue : Prop :=
  forall C : Prop, C -> C.

Definition iFalse : Prop :=
  forall C : Prop, C.

Lemma iand_spec :
  forall P Q : Prop,
    iand P Q <-> P /\ Q.
(* begin hide *)
Proof.
  unfold iand. split.
    intro H. apply H. intros p q. split.
      assumption.
      assumption.
    intros [p q] C H. apply H.
      assumption.
      assumption.
Qed.
(* end hide *)

Lemma ior_spec :
  forall P Q : Prop,
    ior P Q <-> P \/ Q.
(* begin hide *)
Proof.
  unfold ior. split.
    intro H. apply H.
      intro p. left. assumption.
      intro q. right. assumption.
    intros [p | q] C pc qc.
      apply pc. assumption.
      apply qc. assumption.
Qed.
(* end hide *)

Lemma iTrue_spec :
  iTrue <-> True.
(* begin hide *)
Proof.
  unfold iTrue. split.
    intros _. trivial.
    intros _ C c. assumption.
Qed.
(* end hide *)

Lemma iFalse_False :
  iFalse <-> False.
(* begin hide *)
Proof.
  unfold iFalse. split.
    intro H. apply H.
    contradiction.
Qed.
(* end hide *)

Definition iexists (A : Type) (P : A -> Prop) : Prop :=
  forall C : Prop, (forall x : A, P x -> C) -> C.

Lemma iexists_spec :
  forall (A : Type) (P : A -> Prop),
    iexists A P <-> exists x : A, P x.
(* begin hide *)
Proof.
  unfold iexists. split.
    intro H. apply H. intros x p. exists x. assumption.
    intros [x p] C H. apply (H x). assumption.
Qed.
(* end hide *)

Definition ieq {A : Type} (x y : A) : Prop :=
  forall C : Prop, ((x = y) -> C) -> C.

Definition ieq' {A : Type} (x : A) : A -> Prop :=
  fun y : A =>
    forall P : A -> Prop, P x -> P y.

Lemma ieq_spec :
  forall (A : Type) (x y : A),
    ieq x y <-> x = y.
(* begin hide *)
Proof.
  unfold ieq. split.
    intro H. apply H. trivial.
    intros [] C H. apply H. reflexivity.
Qed.
(* end hide *)

Lemma ieq'_spec :
  forall (A : Type) (x y : A),
    ieq' x y <-> x = y.
(* begin hide *)
Proof.
  unfold ieq'. split.
    intro H. apply H. reflexivity.
    intros [] P px. assumption.
Qed.
(* end hide *)

(** * Spójniki pozytywne i negatywne (TODO) *)

(** TODO:
  - implikacja jest negatywna
  - koniunkcja jest negatywna
  - dysjunkcja jest pozytywna
  - fałsz jest pozytywny
  - prawda jest negatywna
  - słaba negacja jest negatywna
  - silna negacja jest pozytywna
  - równoważność jest negatywna
*)

(** * Konkluzja (TODO) *)

(** ** Ściąga *)

(** TODO:
    - [forall x : A, P x] to zdanie mówiące "dla każdego x typu A zachodzi
      P x". Postępujemy z nim tak jak z implikacją, która jest jego
      specjalnym przypadkiem.
    - [exists x : A, P x] to zdanie mówiące "istnieje taki x typu A, który
      spełnia P". Dowodzimy go za pomocą taktyki [exists a], a następnie
      musimy pokazać [P a]. Jeżeli mamy taki dowód w kontekście, możemy
      rozbić go na [a] i [P a] za pomocą taktyki [destruct]. *)

(** #<a class='link'
        href='https://github.com/wkolowski/Typonomikon/blob/master/txt/ściągi/logika.md'>
    Ściąga z rachunku kwantyfikatorów</a># *)

(** * Zadania (TODO) *)

(** Rozwiąż wszystkie zadania jeszcze raz, ale tym razem bez używania komend
    [Module]/[Section]/[Hypothesis] oraz z jak najkrótszymi dowodami

    Inne zadania:
    - modelowanie różnych sytuacji za pomocą zdań i predykatów
    - rozwiązywanie zagadek logicznych
    - więcej zadań z [exists] *)

Section QuantifiersExercises.

Hypotheses
  (A : Type)
  (P Q : A -> Prop)
  (R : Prop).

(** ** Kwantyfikator uniwersalny *)

(** *** Reguły *)

Lemma forall_intro :
  (forall x : A, P x) -> (forall x : A, P x).
(* begin hide *)
Proof. firstorder. Qed.
(* end hide *)

Lemma forall_elim :
  forall x : A, (forall y : A, P y) -> P x.
(* begin hide *)
Proof. firstorder. Qed.
(* end hide *)

(** *** Prawa *)

Lemma forall_nondep :
  (forall x : A, R) <-> (A -> R).
(* begin hide *)
Proof. firstorder. Qed.
(* end hide *)

Lemma forall_and :
  (forall x : A, P x /\ Q x)
    <->
  (forall x : A, P x) /\ (forall x : A, Q x).
(* begin hide *)
Proof. firstorder. Qed.
(* end hide *)

Lemma forall_and_nondep_l :
  forall (A : Type) (P : A -> Prop) (R : Prop),
  (forall x : A, R /\ P x)
    <->
  (A -> R) /\ (forall x : A, P x).
(* begin hide *)
Proof. firstorder. Qed.
(* end hide *)

Lemma forall_and_nondep_r :
  (forall x : A, P x /\ R)
    <->
  (forall x : A, P x) /\ (A -> R).
(* begin hide *)
Proof. firstorder. Qed.
(* end hide *)

Lemma forall_or :
  (forall x : A, P x) \/ (forall x : A, Q x) ->
    (forall x : A, P x \/ Q x).
(* begin hide *)
Proof. firstorder. Qed.
(* end hide *)

Lemma not_forall_or_conv :
  ~
  (forall A P Q,
    (forall x : A, P x \/ Q x) ->
      (forall x : A, P x) \/ (forall x : A, Q x)).
(* begin hide *)
Proof.
  intros H.
  destruct (H bool (fun b => b = true) (fun b => b = false)) as [H' | H'].
  - destruct x; auto.
  - specialize (H' false). congruence.
  - specialize (H' true). congruence.
Qed.
(* end hide *)

Lemma forall_or_nondep_l :
  R \/ (forall x : A, P x) ->
    (forall x : A, R \/ P x).
(* begin hide *)
Proof. firstorder. Qed.
(* end hide *)

Lemma forall_or_nondep_l_conv_classically :
  (forall P : Prop, P \/ ~ P) ->
    (forall x : A, R \/ P x) ->
      R \/ (forall x : A, P x).
(* begin hide *)
Proof.
  intros lem H.
  destruct (lem R) as [r | nr].
  - left; assumption.
  - right. intros x. destruct (H x) as [r | p].
    + contradiction.
    + assumption.
Qed.
(* end hide *)

Lemma forall_or_nondep_r :
  (forall x : A, P x) \/ R ->
    (forall x : A, P x \/ R).
(* begin hide *)
Proof. firstorder. Qed.
(* end hide *)

Lemma forall_or_nondep_r_conv_classically :
  (forall P : Prop, P \/ ~ P) ->
    (forall x : A, P x \/ R) ->
      (forall x : A, P x) \/ R.
(* begin hide *)
Proof.
  intros lem H.
  apply or_comm.
  apply forall_or_nondep_l_conv_classically.
  - assumption.
  - intros x. apply or_comm, H.
Qed.
(* end hide *)

Lemma forall_impl :
  (forall x : A, P x -> Q x) ->
    (forall x : A, P x) -> (forall x : A, Q x).
(* begin hide *)
Proof. firstorder. Qed.
(* end hide *)

Lemma not_forall_impl_conv :
  ~
    (forall (A : Type) (P Q : A -> Prop),
      ((forall x : A, P x) -> (forall x : A, Q x))
        ->
      (forall x : A, P x -> Q x)).
(* begin hide *)
Proof.
  intro H.
  cut (true = false); [inversion 1 |].
  apply (H bool (fun b => b = true) (fun b => b = false)); [| reflexivity].
  intros Heq b; specialize (Heq false); congruence.
Qed.
(* end hide *)

Lemma forall_impl_nondep_l :
  (forall x : A, R -> P x)
    <->
  (R -> forall x : A, P x).
(* begin hide *)
Proof. firstorder. Qed.
(* end hide *)

Lemma forall_impl_nondep_r :
  (forall x : A, P x -> R)
    ->
  ((forall x : A, P x) -> A -> R).
(* begin hide *)
Proof. firstorder. Qed.
(* end hide *)

Lemma forall_not_not :
  ~ ~ (forall x : A, P x) -> (forall x : A, ~ ~ P x).
(* begin hide *)
Proof. firstorder. Qed.
(* end hide *)

(** ** Kwantyfikator egzystencjalny *)

(** *** Reguły *)

Lemma exists_intro :
  forall x : A, P x -> exists y : A, P y.
(* begin hide *)
Proof. firstorder. Qed.
(* end hide *)

Lemma exists_elim :
  (forall x : A, P x -> R) -> (exists y : A, P y) -> R.
(* begin hide *)
Proof. firstorder. Qed.
(* end hide *)

(** *** Prawa *)

Lemma exists_nondep :
  (exists x : A, R) <-> inhabited A /\ R.
(* begin hide *)
Proof. firstorder. Qed.
(* end hide *)

Lemma exists_or :
  (exists x : A, P x \/ Q x)
    <->
  (exists x : A, P x) \/ (exists x : A, Q x).
(* begin hide *)
Proof. firstorder. Qed.
(* end hide *)

Lemma exists_or_nondep_l :
  (exists x : A, R \/ Q x)
    <->
  (inhabited A /\ R) \/ (exists x : A, Q x).
(* begin hide *)
Proof. firstorder. Qed.
(* end hide *)

Lemma exists_or_nondep_r :
  (exists x : A, P x \/ R)
    <->
  (exists x : A, P x) \/ (inhabited A /\ R).
(* begin hide *)
Proof. firstorder. Qed.
(* end hide *)

Lemma ex_and :
  (exists x : A, P x /\ Q x) ->
    (exists y : A, P y) /\ (exists z : A, Q z).
(* begin hide *)
Proof. firstorder. Qed.
(* end hide *)

Lemma not_ex_and_conv :
  ~ (forall (A : Type) (P Q : A -> Prop),
      (exists y : A, P y) /\ (exists z : A, Q z) ->
        (exists x : A, P x /\ Q x)).
(* begin hide *)
Proof.
  intros H.
  destruct (H bool (fun b => b = true) (fun b => b = false)) as (b & Ht & Hf).
  - split.
    + exists true. reflexivity.
    + exists false. reflexivity.
  - congruence.
Restart.
  intros H.
  destruct (H Prop (fun P => P) (fun P => ~ P)) as (S & s & ns).
  - split.
    + exists True. trivial.
    + exists False. intro f. contradiction.
  - contradiction.
Qed.
(* end hide *)

Lemma ex_and_nondep_l :
  (exists x : A, R /\ Q x)
    <->
  R /\ (exists z : A, Q z).
(* begin hide *)
Proof. firstorder. Qed.
(* end hide *)

Lemma ex_and_nondep_r :
  (exists x : A, P x /\ R)
    <->
  (exists x : A, P x) /\ R.
(* begin hide *)
Proof. firstorder. Qed.
(* end hide *)

Lemma not_not_exists :
  (exists x : A, ~ ~ P x) -> ~ ~ (exists x : A, P x).
(* begin hide *)
Proof. firstorder. Qed.
(* end hide *)

(** ** Związki [forall] i [exists] *)

Lemma exists_forall_inhabited :
  A -> (forall x : A, P x) -> exists x : A, P x.
(* begin hide *)
Proof. firstorder. Qed.
(* end hide *)

Lemma not_exists :
  ~ (exists x : A, P x) <-> (forall x : A, ~ P x).
(* begin hide *)
Proof. firstorder. Qed.
(* end hide *)

Lemma exists_not :
  (exists x : A, ~ P x) -> ~ forall x : A, P x.
(* begin hide *)
Proof. firstorder. Qed.
(* end hide *)

Lemma Irrefutable_not_forall :
  (forall P : Prop, P \/ ~ P) ->
    ~ (forall x : A, P x) -> exists x : A, ~ P x.
(* begin hide *)
Proof.
  intros lem nall.
  destruct (lem (exists x : A, ~ P x)).
  - assumption.
  - exfalso. apply nall. intros x. destruct (lem (P x)) as [p | np].
    + assumption.
    + contradict H. exists x. assumption.
Qed.
(* end hide *)

End QuantifiersExercises.

(** ** Zagadki *)

(** **** Ćwiczenie *)

(** Sesshomaru, Naraku i Inuyasha należą do sekty Warring Era. Każdy
    członek tej sekty jest albo demonem, albo człowiekiem, albo i jednym
    i drugim. Żaden człowiek nie lubi deszczu, a wszystkie demony lubią
    śnieg. Naraku nie cierpi wszystkiego, co lubi Sesshomaru, a lubi
    wszystko czego nie lubi Sesshomaru. Sesshomaru lubi deszcz i śnieg.

    Wyraź opis powyższego tekstu w logice pierwszego rzędu. Czy jest
    ktoś, kto jest człowiekiem, ale nie jest demonem? Udowodnij, że
    twoja odpowiedź jest poprawna. *)

(* begin hide *)
Axioms
  (WarringEra : Type)
  (Sesshomaru Naraku Inuyasha : WarringEra)
  (isHuman isDemon : WarringEra -> Prop)
  (Thing : Type)
  (Rain Snow : Thing)
  (likes : WarringEra -> Thing -> Prop)
  (H0 : forall x : WarringEra,
    isHuman x \/ isDemon x \/ (isHuman x /\ isDemon x))
  (H1 : forall x : WarringEra, isHuman x -> ~ likes x Rain)
  (H2 : forall x : WarringEra, isDemon x -> likes x Snow)
  (H3 : forall x : Thing, likes Sesshomaru x -> ~ likes Naraku x)
  (H4 : forall x : Thing, ~ likes Sesshomaru x -> likes Naraku x)
  (H5 : likes Sesshomaru Rain)
  (H6 : likes Sesshomaru Snow).

Lemma isDemon_Sesshomaru :
  isDemon Sesshomaru.
Proof.
  destruct (H0 Sesshomaru) as [H | [D | [H D]]].
  - apply H1 in H. contradict H. exact H5.
  - assumption.
  - assumption.
Qed.

Lemma isHuman_Naraku :
  isHuman Naraku.
Proof.
  destruct (H0 Naraku) as [H | [D | [H D]]].
  - assumption.
  - apply H2 in D. contradict D. apply H3. exact H6.
  - assumption.
Qed.

Lemma not_isDemon_Naraku :
  ~ isDemon Naraku.
Proof.
  intros D. apply H2 in D. contradict D. apply H3. exact H6.
Qed.
(* end hide *)