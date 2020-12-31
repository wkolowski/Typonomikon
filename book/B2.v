(** * B2: Konstruktywny rachunek kwantyfikatorów [TODO] *)

(** * Typy i ich elementy (TODO) *)

(** Tu zestawić ze sobą P : Prop, A : Type, p : P, x : A.

    Wytłumaczyć relację między typami, zdaniami, specyfikacjami
    programów, przestrzeniami, etc. *)

(** * Predykaty i relacje (TODO) *)

(** * Równość - najważniejsza relacja (TODO) *)

(* begin hide *)
Require Export B1.
(*
TODO: Być może coś więcej o równości (i jej alternatywnej definicji?).
TODO: Arystoteles i Leibniz
*)
(* end hide *)

(** Dobrze byłoby zapoznać się z równością przed pierwszym jej użyciem
    w rozdziale o typach induktywnych. *)

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

(** * Kwantyfikatory (TODO) *)

(** ** Kwantyfikator uniwersalny (TODO) *)

(** ** Kwantyfikator egzystencjalny (TODO) *)

(** ** Kwantyfikator unikatowy (TODO) *)

Print unique.
Search unique.

Definition unique {A : Type} (P : A -> Prop) : Prop :=
  exists x : A, P x /\ forall y : A, P y -> x = y.

(** Poznawszy relację równości oraz kwantyfikatory uniwersalny i
    egzystencjalny, możemy zdefiniować inny bardzo ważny "kwantyfikator",
    a mianowicie kwantyfikator unikatowy, który głosi, że istnieje
    dokładnie jeden obiekt spełniający daną właściwość. *)

(** * α-konwersja i inne rodzaje równości (TODO) *)

(** https://github.com/wkolowski/Typonomikon/blob/master/txt/ściągi/równość.md *)

(* begin hide *)
(*
TODO 1: Opisać związki rodzajów równości ze składnią i semantyką
        (empiryczna obserwacja: studenci pierwszego roku nie są
        zbyt płynni w posługiwaniu się składnią _in abstracto_).
TODO 2: Pomysł na jeszcze jeden podrozdział, semantyka vs składnia
TODO 3: Użyć nominalizmów do wytłumaczenia wiązania nazw zmiennych.
*)
(* end hide *)

(** * Konkluzja *)

(** ** Ściąga (TODO) *)

(** TODO:
    - [forall x : A, P x] to zdanie mówiące "dla każdego x typu A zachodzi
      P x". Postępujemy z nim tak jak z implikacją, która jest jego
      specjalnym przypadkiem.
    - [exists x : A, P x] to zdanie mówiące "istnieje taki x typu A, który
      spełnia P". Dowodzimy go za pomocą taktyki [exists a], a następnie
      musimy pokazać [P a]. Jeżeli mamy taki dowód w kontekście, możemy
      rozbić go na [a] i [P a] za pomocą taktyki [destruct]. *)

(** https://github.com/wkolowski/Typonomikon/blob/master/txt/ściągi/logika.md *)

(** * Zadania (TODO) *)

(** rozwiąż wszystkie zadania jeszcze raz, ale tym razem bez używania
    Module/Section/Hypothesis oraz z jak najkrótszymi dowodami

    Inne zadania:
    - modelowanie różnych sytuacji za pomocą zdań i predykatów
    - rozwiązywanie zagadek logicznych
    - więcej zadań z exists *)

(** ** Prawa *)

Section QuantifiersExercises.

Variable A : Type.
Hypotheses P Q : A -> Prop.

(** *** Projekcje *)

Lemma forall_and_proj1 :
  (forall x : A, P x /\ Q x) -> (forall x : A, P x).
(* begin hide *)
Proof.
  intros. destruct (H x). assumption.
Qed.
(* end hide *)

Lemma forall_and_proj2 :
  (forall x : A, P x /\ Q x) -> (forall x : A, Q x).
(* begin hide *)
Proof.
  intros. destruct (H x). assumption.
Qed.
(* end hide *)

(** *** Rozdzielność *)

Lemma forall_dist_and :
  (forall x : A, P x /\ Q x) <->
  (forall x : A, P x) /\ (forall x : A, Q x).
(* begin hide *)
Proof.
  split.
    intros. split.
      intros. destruct (H x). assumption.
      intros. destruct (H x). assumption.
    intros. split.
      destruct H. apply H.
      destruct H. apply H0.
Restart.
  split; intros; split; intros; try destruct H; try (destruct (H x));
  try assumption; try apply H; try apply H0.
Qed.
(* end hide *)

Lemma exists_dist_or :
  (exists x : A, P x \/ Q x) <->
  (exists x : A, P x) \/ (exists x : A, Q x).
(* begin hide *)
Proof.
  split; intros.
    destruct H as [x [HP | HQ]].
      left. exists x. assumption.
      right. exists x. assumption.
    destruct H as [[x HP] | [x HQ]].
      exists x. left. assumption.
      exists x. right. assumption.
Restart.
  split; intros.
    destruct H as [x [HP | HQ]];
      [left | right]; exists x; assumption.
    destruct H as [[x HP] | [x HQ]];
      exists x; [left | right]; assumption.
Qed.
(* end hide *)

Lemma ex_dist_and :
  (exists x : A, P x /\ Q x) ->
    (exists y : A, P y) /\ (exists z : A, Q z).
(* begin hide *)
Proof.
  intros. destruct H as [x H]. destruct H.
  split; exists x; assumption.
Qed.
(* end hide *)

(** *** Inne *)

Lemma forall_or_imp :
  (forall x : A, P x) \/ (forall x : A, Q x) ->
    forall x : A, P x \/ Q x.
(* begin hide *)
Proof.
  destruct 1; intros.
    left. apply H.
    right. apply H.
Restart.
  destruct 1; intros; [left | right]; apply H.
Qed.
(* end hide *)

Lemma forall_imp_imp :
  (forall x : A, P x -> Q x) ->
    (forall x : A, P x) -> (forall x : A, Q x).
(* begin hide *)
Proof.
  intros. apply H. apply H0.
Qed.
(* end hide *)

Lemma forall_inhabited_nondep :
  forall R : Prop, A -> ((forall x : A, R) <-> R).
(* begin hide *)
(* TODO: wyrzucić *)
Proof.
  split; intros.
    apply H. assumption.
    assumption.
Restart.
  split; intros; try apply H; assumption.
Qed.
(* end hide *)

Lemma forall_or_nondep :
  forall R : Prop,
    (forall x : A, P x) \/ R -> (forall x : A, P x \/ R).
(* begin hide *)
Proof.
  destruct 1; intros.
    left. apply H.
    right. assumption.
Qed.
(* end hide *)

Lemma forall_nondep_impl :
  forall R : Prop,
    (forall x : A, R -> P x) <-> (R -> forall x : A, P x).
(* begin hide *)
Proof.
  split; intros.
    apply H. assumption.
    apply H. assumption.
Restart.
  split; intros; apply H; assumption.
Qed.
(* end hide *)

End QuantifiersExercises.


(** ** Zagadki *)

(** **** Ćwiczenie *)

(* begin hide *)
(*
Definition Classically (A : Type) : Type :=
  (forall P : Prop, P \/ ~ P) -> A.

Notation "f $ x" := (f x) (at level 100, only parsing).

Ltac cls := progress unfold Classically; intro LEM.
*)
(* end hide *)

From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
  elim: (H0 Sesshomaru) => [| [| []]];
  by try move/(@H1 _)/(_ H5) => [].
Qed.

Lemma isHuman_Naraku :
  isHuman Naraku.
Proof.
  elim: (H0 Naraku) => [| [| []]]; try done.
    by move/(@H2 _)/(H3 H6).
Qed.

Lemma not_isDemon_Naraku :
  ~ isDemon Naraku.
Proof.
  by move/H2/(H3 H6).
Qed.
(* end hide *)