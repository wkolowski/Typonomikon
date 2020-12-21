(** * B1: Konstruktywny rachunek zdań [TODO] *)

Require Export B0.

(** * Zdania i spójniki logiczne (TODO) *)

(** ** Implikacja (TODO) *)

(* begin hide *)
(* TODO: rozumowania w przód i w tył, czyli
  [apply] i [apply ... in ...] *)
(* end hide *)

(* begin hide *)
(* rozumowanie od tyłu jest lepsze, logika jest bezmyślna *)
(* end hide *)

(** ** Dysjunkcja (TODO) *)

(** ** Koniunkcja (TODO) *)

(** ** Prawda i fałsz (TODO) *)

(* begin hide *)
(* TODO: wspomnieć, że to 0-arne wersje dysjunkcji i koniunkcji *)
(* end hide *)

(** ** Równoważność (TODO) *)

(** ** Negacja (TODO) *)

(** ** Silna negacja *)

(* begin hide *)
(** TODO: przepisać rozdział o silnej negacji

    Nowy pomysł: to samo co ostatnio, czyli dwie laseczki, ale tym razem
    podkreślić, że silna negacja znaczy "któreś zdanie nie zachodzi",
    zaś słaba negacja znaczy "zdania są ze sobą niekompatybilne".

    Nawiązać do aksjomatu [WLEM] ([P] i [~ P] są ze sobą niekompatybilne,
    ale silna negacja [~ P \/ ~ ~ P] jest tabu).

    Są też negacje pośrednie, co widać przy większej liczbie koniunktów,
    np. dla zdania [P /\ Q /\ R]:
    - [~ P \/ ~ Q \/ ~ R] - silna negacja, "któreś nie zachodzi"
    - [P /\ Q /\ R -> False] - słaba negacja, "wszystkie niekompatybilne"
    - [P /\ Q -> False] - pośrednia negacja, "niektóre niekompatybilne"
*)
(* end hide *)

(** Poznaliśmy uprzednio pewien spójnik, zapisywany wdzięcznym wygibaskiem
    [~], a zwany górnolotnie negacją. Powinniśmy się jednak zastanowić: czy
    spójnik ten jest dla nas zadowalający? Czy pozwala on nam wyrażać nasze
    przemyślenia w najlepszy możliwy sposób?

    Jeżeli twoja odpowiedź brzmi "tak", to uroczyście oświadczam, że wcale
    nie masz racji. Wyobraźmy sobie następującą sytuację: jesteśmy psycho
    patusem, próbującym pod pozorem podrywu poobrażać przeróżne panienki.

    Podbijamy do pierwszej z brzegu, która akurat jest normalną dziewczyną,
    i mówimy: "Hej mała, jesteś gruba i mądra". Nasza oburzona rozmówczyni,
    jako że jest szczupła, odpowiada nam: "Wcale nie jestem gruba. Spadaj
    frajerze".

    Teraz na cel bierzemy kolejną, która siedzi sobie samotnie przy stoliku
    w Starbuniu, popija kawkę z papierowego kubka i z uśmiechem na ustach
    próbuje udowodnić w Coqu jakieś bardzo skomplikowane twierdzenie.
    Podbijamy do niej i mówimy: "Hej mała, jesteś gruba i mądra". Jako, że
    ona też jest szczupła, oburza się i odpowiada nam tak:

    "Czekaj, czekaj, Romeo. Załóżmy, że twój tani podryw jest zgodny z
    prawdą. Gdybym była gruba i mądra, to byłabym w szczególności mądra,
    bo P i Q implikuje Q. Ale gdybym była mądra, to wiedziałabym, żeby
    tyle nie żreć, a skoro tak, to bym nie żarła, więc nie byłabym gruba,
    ale na mocy założenia jestem, więc twój podryw jest sprzeczny. Jeżeli
    nie umiesz logiki, nie idę z tobą do łóżka."

    Widzisz różnicę w tych dwóch odpowiedziach? Pierwsza z nich wydaje nam
    się bardzo naturalna, bo przypomina zaprzeczenia, jakich zwykli ludzie
    używają w codziennych rozmowach. Druga wydaje się zawoalowana i bardziej
    przypomina dowód w Coqu niż codzienne rozmowy. Między oboma odpowiedziami
    jest łatwo zauważalna przepaść.

    Żeby zrozumieć tę przepaść, wprowadzimy pojęcia silnej i słabej negacji.
    W powyższym przykładzie silną negacją posłużyła się pierwsza dziewczyna -
    silną negacją zdania "jesteś gruba i mądra" jest tutaj zdanie "wcale nie
    jestem gruba". Oczywiście jest też druga możliwość silnego zaprzeczenia
    temu zdaniu - "nie jestem mądra" - ale z jakichś powodów to zaprzeczenie
    nie padło. Ciekawe dlaczego? Druga dziewczyna natomiast posłużyła się
    słabą negacją, odpowiadając "gdybym była gruba i mądra, to... (tutaj
    długaśne rozumowanie)... więc sprzeczność".

    Słaba negacja to ta, którą już znamy, czyli Coqowe [not]. Ma ona
    charakter hipotetyczny, gdyż jest po prostu implikacją, której
    konkluzją jest [False]. W rozumowaniach słownych sprowadza się ona
    do schematu "gdyby tak było, to wtedy...".

    Silna negacja to najbardziej bezpośredni sposób zaprzeczenia danemu
    zdaniu. W Coqu nie ma żadnego spójnika, który ją wyraża, bo ma ona
    charakter dość ad hoc - dla każdego zdania musimy sami sobie wymyślić,
    jak brzmi zdanie, które najsilniej mu przeczy. W rozumowaniach słownych
    silna negacja sprowadza się zazwyczaj do schematu "nie jest tak".

    Spróbujmy przetłumaczyć powyższe rozważania na język logiki. Niech
    [P] oznacza "gruba", zaś [Q] - "mądra". Silną negacją zdania [P /\ Q]
    jest zdanie [~ P \/ ~ Q] ("nie gruba lub nie mądra"), zaś jego słabą
    negacją jest [~ (P /\ Q)], czyli [P /\ Q -> False] ("jeżeli gruba i
    mądra, to sprzeczność").

    Zauważmy, że o ile słaba negacja jest uniwersalna, tj. słabą negacją
    [P /\ Q] zawsze jest [~ (P /\ Q)], to silna negacja jest ad hoc w tym
    sensie, że gdyby [P] było postaci [P1 /\ P2], to wtedy silną negacją
    [P /\ Q] nie jest już [~ P \/ ~ Q], a [~ P1 \/ ~ P2 \/ ~ Q] - żeby
    uzyskać silną negację, musimy zanegować [P] silnie, a nie słabo.

    Dlaczego silna negacja jest silna, a słaba jest słaba, tzn. dlaczego
    nazwaliśmy je tak a nie inaczej? Wyjaśnia to poniższe twierdzenie oraz
    następująca po nim beznadziejna próba udowodnienia analogicznego
    twierdzenia z implikacją idącą w drugą stronę. *)

Lemma strong_to_weak_and :
  forall P Q : Prop, ~ P \/ ~ Q -> ~ (P /\ Q).
Proof.
  intros P Q Hor Hand.
  destruct Hand as [p q].
  destruct Hor as [notp | notq].
    apply notp. assumption.
    apply notq. assumption.
Qed.

(** Jak widać, silna negacja koniunkcji pociąga za sobą jej słabą negację.
    Powód tego jest prosty: jeżeli jeden z koniunktów nie zachodzi, ale
    założymy, że oba zachodzą, to w szczególności każdy z nich zachodzi
    osobno i mamy sprzeczność.

    A czy implikacja w drugą stronę zachodzi? *)

Lemma weak_to_strong_and :
  forall P Q : Prop, ~ (P /\ Q) -> ~ P \/ ~ Q.
Proof.
  intros P Q notpq. left. intro p. apply notpq. split.
    assumption.
Abort.

(** Jak widać, nie udało nam się udowodnić odwrotnej implikacji i to wcale
    nie dlatego, że jesteśmy mało zdolni - po prostu konstruktywnie nie da
    się tego zrobić.

    Powód tego jest prosty: jeżeli wiemy, że [P] i [Q] razem prowadzą do
    sprzeczności, to wiemy zdecydowanie za mało. Mogą być dwa powody:
    - [P] i [Q] mogą bez problemu zachodzić osobno, ale być sprzeczne
      razem
    - nawet jeżeli któryś z koniunktów prowadzi do sprzeczności, to nie
      wiemy, który

    Żeby zrozumieć pierwszą możliwość, niech [P] oznacza "siedzę", a [Q] -
    "stoję". Rozważmy zdanie [P /\ Q], czyli "siedzę i stoję". Żeby nie było
    za łatwo załóżmy też, że znajdujesz się po drugiej stronie kosmosu i mnie
    nie widzisz.

    Oczywiście nie mogę jednocześnie siedzieć i stać, gdyż czynności te się
    wykluczają, więc możesz skonkludować, że [~ (P /\ Q)]. Czy możesz jednak
    wywnioskować stąd, że [~ P \/ ~ Q], czyli że "nie siedzę lub nie stoję"?
    Konstruktywnie nie, bo będąc po drugiej stronie kosmosu nie wiesz, której
    z tych dwóch czynności nie wykonuję.

    Z drugim przypadkiem jest tak samo, jak z końcówką powyższego przykładu:
    nawet jeżeli zdania [P] i [Q] się wzajemnie nie wykluczają i niesłuszność
    [P /\ Q] wynika z tego, że któryś z koniunktów nie zachodzi, to możemy po
    prostu nie wiedzieć, o który z nich chodzi.

    Żeby jeszcze wzmocnić nasze zrozumienie, spróbujmy w zaskakujący sposób
    rozwinąć definicję (słabej) negacji dla koniunkcji: *)

Lemma not_and_surprising :
  forall P Q : Prop, ~ (P /\ Q) <-> (P -> ~ Q).
Proof.
  split.
    intros npq p q. apply npq. split.
      assumption.
      assumption.
    intros pnq pq. destruct pq as [p q]. apply pnq.
      assumption.
      assumption.
Qed.

(** I jeszcze raz... *)

Lemma not_and_surprising' :
  forall P Q : Prop, ~ (P /\ Q) <-> (Q -> ~ P).
(* begin hide *)
Proof.
  split.
    intros npq p q. apply npq. split.
      assumption.
      assumption.
    intros qnp pq. destruct pq as [p q]. apply qnp.
      assumption.
      assumption.
Qed.
(* end hide *)

(** Jak (mam nadzieję) widać, słaba negacja koniunkcji nie jest niczym
    innym niż stwierdzeniem, że oba koniunkty nie mogą zachodzić razem.
    Jest to więc coś znacznie słabszego, niż stwierdzenie, że któryś z
    koniunktów nie zachodzi z osobna. *)

Lemma mid_neg_conv :
  forall P Q : Prop, ~ (P /\ Q) -> ((P -> ~ Q) /\ (Q -> ~ P)).
Proof.
  firstorder.
Qed.

(** Jak napisano w Piśmie, nie samą koniunkcją żyje człowiek. Podumajmy
    więc, jak wygląda silna negacja dysjunkcji. Jeżeli chcemy dosadnie
    powiedzieć, że [P \/ Q] nie zachodzi, to najprościej powiedzieć:
    [~ P /\ ~ Q]. Słaba negacja dysjunkcji ma zaś rzecz jasna postać
    [~ (P \/ Q)]. *)

Lemma strong_to_weak_or :
  forall P Q : Prop, ~ P /\ ~ Q -> ~ (P \/ Q).
Proof.
  do 2 destruct 1; contradiction.
Qed.

(** Co jednak dość ciekawe, silna negacja nie zawsze jest silniejsza
    od słabej (ale z pewnością nie może być od niej słabsza - gdyby
    mogła, to nazywałaby się inaczej). W przypadku dysjunkcji obie
    negacje są równoważne, co obrazuje poniższe twierdzenie, które
    głosi, że słaba negacja implikuje silną (a to razem z powyższym
    daje równoważność): *)

Lemma weak_to_strong_or :
  forall P Q : Prop, ~ (P \/ Q) -> ~ P /\ ~ Q.
Proof.
  split; intro; apply H; [left | right]; assumption.
Qed.

(** Wynika to z faktu, że [~ P /\ ~ Q] to tak naprawdę para implikacji
    [P -> False] i [Q -> False], zaś [~ (P \/ Q)] to... gdy pomyślimy
    nad tym odpowiednio mocno... ta sama para implikacji. Jest tak
    dlatego, że jeżeli [P \/ Q] implikuje [R], to umieć wyprodukować
    [R] musimy zarówno z samego [P], jak i z samego [Q]. *)


Lemma deMorgan_dbl_neg :
  (forall P Q : Prop, ~ (P /\ Q) -> ~ P \/ ~ Q) <->
  (forall P : Prop, ~ ~ P -> P).
Proof.
  split.
    intros deMorgan P H.
Abort.

(** ** Czy Bozia dała inne spójniki logiczne? (TODO) *)

(* begin hide *)
(* TODO: tutaj opisać słabe "lub" oraz "xor" *)
(* end hide *)

(** * O czym nie wolno mówić zdaniom logicznym *)

(** ** Paradoks pieniądza i kebaba *)

(** Przestrzegłem cię już przed nieopatrznym interpretowaniem zdań języka
    naturalnego za pomocą zdań logiki formalnej. Gdybyś jednak wciąż
    był skłonny to robić, przyjrzyjmy się kolejnemu "paradoksowi". *)

Lemma copy :
  forall P : Prop, P -> P /\ P.
(* begin hide *)
Proof.
  split; assumption.
Qed.
(* end hide *)

(** Powyższe niewinnie wyglądające twierdzenie mówi nam, że [P] implikuje
    [P] i [P]. Spróbujmy przerobić je na paradoks, wymyślając jakąś wesołą
    interpretację dla [P].

    Niech zdanie [P] znaczy "mam złotówkę". Wtedy powyższe twierdzenie mówi,
    że jeżeli mam złotówkę, to mam dwa złote. Widać, że jeżeli jedną z tych
    dwóch złotówek znów wrzucimy do twierdzenia, to będziemy mieli już trzy
    złote. Tak więc jeżeli mam złotówkę, to mam dowolną ilość pieniędzy.

    Dla jeszcze lepszego efektu powiedzmy, że za 10 złotych możemy kupić
    kebaba. W ostatecznej formie nasze twierdzenie brzmi więc: jeżeli mam
    złotówkę, to mogę kupić nieograniczoną ilość kebabów.

    Jak widać, logika formalna (przynajmniej w takiej postaci, w jakiej ją
    poznajemy) nie nadaje się do rozumowania na temat zasobów. Zasobów, bo
    tym właśnie są pieniądze i kebaby. Zasoby to byty, które można
    przetwarzać, przemieszczać i zużywać, ale nie można ich kopiować i
    tworzyć z niczego. Powyższe twierdzenie dobitnie pokazuje, że zdania
    logiczne nie mają nic wspólnego z zasobami, gdyż ich dowody mogą być
    bez ograniczeń kopiowane. *)

(* begin hide *)
Fixpoint andn (n : nat) (P : Prop) : Prop :=
match n with
    | 0 => True
    | S n' => P /\ andn n' P
end.

Lemma one_to_many :
  forall (n : nat) (P : Prop),
    P -> andn n P.
Proof.
  induction n as [| n']; cbn; intros.
    trivial.
    split; try apply IHn'; assumption.
Qed.

Lemma buy_all_kebabs :
  forall P Q : Prop,
    (andn 10 P -> Q) -> P -> forall n : nat, andn n Q.
Proof.
  intros P Q H p n. revert P Q H p.
  induction n as [| n']; cbn; intros.
    trivial.
    split.
      apply H. apply (one_to_many 10 P). assumption.
      apply (IHn' P Q H p).
Qed.
(* end hide *)

(** **** Ćwiczenie (formalizacja paradoksu) *)

(** UWAGA TODO: to ćwiczenie wymaga znajomości rozdziału 2, w szczególności
    indukcji i rekursji na liczbach naturalnych.

    Zdefiniuj funkcję [andn : nat -> Prop -> Prop], taką, że [andn n P]
    to n-krotna koniunkcja zdania [P], np. [andn 5 P] to
    [P /\ P /\ P /\ P /\ P]. Następnie pokaż, że [P] implikuje [andn n P]
    dla dowolnego [n].

    Na końcu sformalizuj resztę paradoksu, tzn. zapisz jakoś, co to znaczy
    mieć złotówkę i że za 10 złotych można kupić kebaba. Wywnioskuj stąd,
    że mając złotówkę, możemy kupić dowolną liczbę kebabów.

    Szach mat, Turcjo bankrutuj! *)

(** ** Paradoks Curry'ego *)

Lemma Curry's_paradox :
  forall P Q : Prop,
    (P <-> (P -> Q)) -> Q.
Proof.
  destruct 1.
  apply H.
    apply H0. intro. apply H; assumption.
    apply H0. intro. apply H; assumption.
Qed.

(** **** Ćwiczenie *)

(** TODO: napisać polecenie *)

(* begin hide *)
Lemma mutual_reference :
  forall P Q : Prop,
    (P <-> (Q <-> True)) ->
    (Q <-> (P <-> False)) ->
      False.
Proof.
  firstorder.
Qed.
(* end hide *)


(** * Zadania (TODO) *)

(** - na koniec dać tylko te zadania, które łączą wiele spójników
    - dodać zadanie dotyczące czytania twierdzeń i dowodów
    - dodać zadania dotyczące czytania formuł (precedencja etc.) *)

(** * Ściąga *)