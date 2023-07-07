(** * D2z: Dobre, złe i podejrzane typy induktywne *)

Require Import Arith.

From Typonomikon Require Import D1.

(** Poznana przez nas dotychczas definicja typów induktywnych (oraz wszelkich
    ich ulepszeń, jak indukcja-indukcja, indukcja-rekursja etc.) jest
    niepełna. Tak jak świat pełen jest złoczyńców oszukujących starszych
    ludzi metodą "na wnuczka", tak nie każdy typ podający się za induktywny
    faktycznie jest praworządnym obywatelem krainy typów induktywnych.

    Na szczęście typy induktywne to istoty bardzo prostolinijne, zaś te złe
    można odróżnić od tych dobrych gołym okiem, za pomocą bardzo prostego
    kryterium: złe typy induktywne to te, które nie są ściśle pozytywne.
    Zanim jednak dowiemy się, jak rozpoznawać złe typy induktywne, poznajmy
    najpierw dwa powody, przez które złe typy induktywne są złe.

    Przyjrzyjmy się poniższemu typowemu przypadkowi negatywnego typu
    induktywnego (co dokładnie znaczy w tym kontekście słowo "negatywny"
    i jak takie typy rozpoznawać zobaczymy później): *)

Fail Inductive wut (A : Type) : Type :=
| C : (wut A -> A) -> wut A.

(* ===> The command has indeed failed with message:
        Non strictly positive occurrence of "wut"
        in "(wut A -> A) -> wut A". *)

(** Uwaga: poprzedzenie komendą [Fail] innej komendy oznajmia Coqowi, że
    spodziewamy się, iż komenda zawiedzie. Coq akceptuje komendę [Fail c],
    jeżeli komenda [c] zawodzi, i wypisuje jej komunikat o błędzie. Jeżeli
    komenda [c] zakończy się sukcesem, komenda [Fail c] zwróci błąd.
    Komenda [Fail] jest przydatna w sytuacjach takich jak obecna, gdy
    chcemy zilustrować fakt, że jakaś komenda zawodzi.

    W naszym przypadku komenda [Fail] kończy się sukcesem, a zatem próba
    zdefiniowania powyższego typu induktywnego się nie powiodła. Wiadomość
    o błędzie podaje nam, jak na tacy, powód tej sytuacji: typ konstruktora
    [C] zawiera nie-ściśle-pozytywne wystąpienie definiowanego typu [wut A].

    Komenda [Fail c] ma też jednak pewne wady: poza poświadczeniem rezultatu
    wykonania komendy [c], nie ma ona żadnych innych skutków. To sprawia, że
    użycie [Fail] zmusiłoby nas, w dalszej części podrozdziału, do zaledwie
    udawania, że mamy jakiś typ i coś z nim robimy. To zaś jest bardzo złe,
    bo bez czujnego Coqowego oka bardzo łatwo jest napisać coś głupiego lub
    popełnić jakiś inny błąd. *)

Module wut.

Unset Positivity Checking.
Inductive wut (A : Type) : Type :=
| C : (wut A -> A) -> wut A.
Set Positivity Checking.

(** Na szczęście jest sposób na to, byśmy mogli pobawić się nie-ściśle-pozytywnymi
    typami induktywnymi pod czujnym okiem Coqa: posługując się komendą [Unset
    Positivity Checking] możemy wyłączyć positivity checker (czyli po polsku
    "sprawdzacz pozytywności"), co sprawi, że Coq zaakceptuje definicję typu [wut].
    Dzięki temu będziemy mogli posługiwać się tym typem jak gdyby nigdy nic.

    Oczywiście takie rozwiązanie również niesie za sobą negatywne konsekwencje:
    jak za chwilę zobaczymy, z istnienia typu [wut] można wywnioskować dowód
    fałszu, a zatem od teraz możemy udowodnić w Coqu dosłownie wszystko, więc
    teoretycznie wszystkie nasze dowody stają się bezwartościowe. W praktyce
    rzecz jasna nie będziemy tej sprzeczności wykorzystywać w niecnych celach,
    a istnienie typu [wut A] dopuszczamy tylko w celach ilustracyjnych. *)

(** * Nieterminacja jako źródło zła na świecie *)

(** Pierwszym powodem nielegalności nie-ściśle-pozytywnych typów induktywnych
    jest to, że unieważniają one filozoficzną interpretację teorii typów i
    pozwalają łamać reguły dzięki którym to co robimy w Coqu ma jakikolwiek
    sens (co jednak tylko czasami prowadzi do sprzeczności bezpośrednio).
    Przyjrzyjmy się poniższemu programowi: *)

Definition loop (A : Type) : A :=
  let f (w : wut A) : A :=
    match w with
    | C _ g => g w
    end
  in f (C _ f).

(** Już sam typ tego programu wygląda złowrogo: dla każdego typu [A] program
    zwraca element typu [A]. Nie dziwota więc, że możemy uzyskać z niego dowód
    fałszu wstawiając [False] za [A]. *)

Definition santa_is_a_pedophile : False := loop False.

(** Paradoksalnie jednak to nie ta rażąca sprzeczność jest naszym największym
    problemem - nie z każdego złego typu induktywnego da się tak łatwo dostać
    sprzeczność (systematyczny sposób dostawania sprzeczności z istnienia
    takich typów zobaczymy później). W rzeczywistości jest nim nieterminacja.

    Nieterminacja (ang. nontermination) lub kolokwialniej zapętlenie to sytuacja,
    w której program nigdy nie skończy się wykonywać. Ta właśnie bolączka jest
    przypadłością [loop], czego nietrudno domyślić się po nazwie.

    Dlaczego [loop] nie terminuje? Przyjrzyjmy się definicji: za pomocą [let]a
    definiujemy funkcję [f : wut A -> A], która odpakowuje swój argument [w],
    wyciąga z niego funkcję [g : wut A -> A] i aplikuje [g] do [w], czyli do
    oryginalnego argumentu [f]. Wynikiem całego programu jest [f] zaaplikowane
    do siebie samego zawiniętego w konstruktor [C] (żeby typy się zgadzały).

    Ta aplikacja czegoś do samego siebie to kolejny sygnał ostrzegawczy, który
    powinien wzbudzić naszą czujność. Ogólniej sytuacja, w której coś odnosi
    się samo do siebie, nazywa się autoreferencją i często prowadzi do różnych
    wesołych paradoksów.

    Żeby jeszcze lepiej zrozumieć nieterminację [loop], spróbujmy interaktywnie
    prześledzić, w jaki sposób program ten się oblicza. *)

Goal loop unit = tt.
Proof.
  cbv delta [loop].
  cbv beta.
  cbv zeta.

  cbv beta. cbv iota.
  cbv beta. cbv iota.
  cbv beta; cbv iota.
Abort.

(** Jeżeli jesteś leniwy i nie masz włączonego CoqIDE, sprowadza się to do czegoś
    w tym stylu:

    [loop A =]

    [let f := ... in f (C f) =]

    [let f := ... in match C f with | C g => g (C f) end =]

    [let f := ... in f (C f)]

    i tak dalej.

    To natomiast, co powinno nas tu zdziwić, to fakt, że [loop] jest funkcją
    w pewnym sensie rekurencyjną (bo funkcja [f] wywołuje sama siebie), mimo
    że przecież nie użyliśmy komendy [Fixpoint]!

    To jest właśnie jeden z przejawów zamętu, jaki wprowadzają negatywny typy
    induktywne - zmieniają reguły gry. Dotychczas [Fixpoint] (i [fix]) dawały
    nam możliwość użycia rekursji (a w praktyce oznaczały, że rekursji faktycznie
    użyliśmy), zaś [Definition] (i [fun]) świadczyło o tym, że funkcja nie jest
    rekurencyjna. Od kiedy tylko Coq zaakceptował definicję typu [wut A], regułę
    tę można bez przeszkód łamać, z opłakanymi konsekwencjami.

    Przyjrzyjmy się teraz problemom filozoficznym powodowanym przez
    nieterminację. W skrócie: zmienia ona fundamentalne właściwości
    obliczeń, co prowadzi do zmiany interpretacji pojęcia typu, zaś
    to pociąga za sobą kolejne przykre skutki, takie jak np. to, że
    reguły eliminacji tracą swoje uzasadnienie. Brzmi mega groźnie,
    prawda?

    Na szczęście tak naprawdę, to sprawa jest prosta. W Coqu wymagamy,
    aby każde obliczenie się kończyło. Końcowe wyniki obliczeń (zwane też
    wartościami, postaciami kanonicznymi lub postaciami normalnymi) możemy
    utożsamiać z elementami danego typu. Dla przykładu wynikami obliczania
    termów typu [bool] są [true] i [false], więc możemy myśleć, że są to
    elementy typu [bool] i [bool] składa się tylko z nich. To z kolei daje
    nam uzasadnienie reguły eliminacji (czyli indukcji) dla typu [bool]:
    żeby udowodnić [P : bool -> Prop] dla każdego [b : bool], wystarczy
    udowodnić [P true] i [P false], gdyż [true] i [false] są jedynymi
    elementami typu [bool].

    Nieterminacja obraca tę jakże piękną filozoficzną wizję w perzynę:
    nie każde obliczenie się kończy, a przez to powstają nowe, "dziwne"
    elementy różnych typów. [loop bool] nigdy nie obliczy się do [true] ani
    do [false], więc możemy traktować je jako nowy element typu [bool]. To
    sprawia, że [bool], typ z założenia dwuelementowy, ma teraz co najmniej
    trzy elementy - [true], [false] i [loop bool]. Z tego też powodu reguła
    eliminacji przestaje obowiązywać, bo wymaga ona dowodów jedynie dla
    [true] i [false], ale milczy na temat [loop bool]. Moglibyśmy próbować
    naiwnie ją załatać, uwzględniając ten dodatkowy przypadek, ale tak po
    prawdzie, to nie wiadomo nawet za bardzo jakie jeszcze paskudztwa
    rozpanoszyły się w typie [bool] z powodu nieterminacji.

    Morał jest prosty: nieterminacja to wynalazek szatana, a negatywne
    typy induktywne to też wynalazek szatana. *)

(** **** Ćwiczenie *)

(** Użyj typu [wut nat] żeby zdefiniować nieskończoną liczbę naturalną [omega]
    (jeżeli szukasz inspiracji, zerknij na definicję [loop]). Następnie udowodnij,
    że [omega] jest większa od każdej innej liczby naturalnej. *)

(* begin hide *)
Definition f (w : wut.wut nat) : nat :=
  S match w with
    | wut.C _ g => g w
    end.

Definition omega : nat :=
  f (wut.C _ f).
(* end hide *)

Lemma lt_n_omega :
  forall n : nat, n < omega.
(* begin hide *)
Proof.
  induction n as [| n'].
    apply le_n_S, Nat.le_0_l.
    now apply Nat.succ_lt_mono in IHn'.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Jakie elementy ma typ [nat]? Wypisz kilka początkowych, a potem opisz
    ogólną zasadę ich powstawania.

    Napisz jakiś term [t : nat], który nie jest wartością, ale terminuje.
    Jaki jest wynik obliczenia tego termu?

    Następnie przyjrzyj się termowi [loop nat]. Czy term ten terminuje?
    Pobaw się nim w trybie dowodzenia, żeby się przekonać (że nie, bo
    niby czego innego się spodziewałeś?).

    Przypomnij sobie regułę indukcji dla [nat]. Gdyby udowodnić przez
    indukcję [forall n : nat, P n], jak wygląda dowód [P t], gdzie [t]
    to term, który napisałeś powyżej? A jak wygląda dowód [P (loop nat)]? *)

(** **** Ćwiczenie *)

(** Spróbujmy lepiej zrozumieć, o co chodzi z tym, że reguły eliminacji "tracą
    swoje uzasadnienie": udowodnij, że dla każdej liczby naturalnej istnieje
    liczba od niej większa (zdaje się, że już to przerabialiśmy). *)

Lemma no_greatest :
  forall n : nat, exists m : nat, n < m.
(* begin hide *)
Proof.
  induction n as [| n' [m IH]].
    exists 1. apply le_n.
    exists (S m).
      now apply Nat.succ_lt_mono in IH.
Qed.
(* end hide *)

(** Jak to możliwe, że udało nam się udowodnić to twierdzenie, skoro przecież
    w poprzedinm ćwiczeniu udowodniliśmy, że największą liczbą naturalną jest
    [omega]?

    Ano, [omega] jest niestandardową liczbą naturalną - pomiotem szatana
    powstałym w wyniku nieterminacji - i w związku z tym indukcja milczy
    na jej temat. Parafrazując: żeby udowodnić coś dla wszystkich liczb
    naturalnych przez indukcję, w ogóle nie musimy przejmować się omegą.
    Chyba nie trzeba dodawać, że to kolejna droga prowadząca prosto do
    sprzeczności? *)

Lemma yes_and_no : False.
Proof.
  destruct (no_greatest omega) as [n H1].
  assert (H2 := lt_n_omega n).
  apply Nat.lt_asymm in H1.
  contradiction.
Qed.

End wut.

(** Żeby przez przypadek nie użyć żadnej ze sprzeczności, które daje nam typ
    [wut], schowaliśmy je w osobnym module, też nazwanym [wut]. Oczywiście
    wciąż mamy do nich dostęp, ale teraz ciężej będzie nam się pomylić. *)

(** * Twierdzenie Cantora *)

(** Zanim zaczniemy ten podrozdział na poważnie, mam dla ciebie wesoły
    łamaniec językowy:

    Cantor - kanciarz, który skradł zza kurtyny kantoru z Kantonu kontury
    kartonu Koranicznemu kanarowi, który czasem karał karczystych kafarów
    czarami za karę za kantowanie i za zakatowanie zza kontuaru konarem
    kontrkulturowych kuluarowych karłów.

    Dobra, wystarczy. Reszta tego podrozdziału będzie śmiertelnie poważna,
    a przyjrzymy się w niej jednemu z mega klasycznych twierdzeń z końca
    XIX w. głoszącemu mniej więcej, że "zbiór potęgowy zbioru liczb
    naturalnych ma większą moc od zbioru liczb naturalnych".

    Co za bełkot, pomyślisz zapewne. Ten podrozdział poświęcimy właśnie temu,
    żeby ów bełkot nieco wyklarować. Jeżeli zaś zastanawiasz się, po co nam
    to, to odpowiedź jest prosta - na (uogólnionym) twierdzeniu Cantora
    opierać się będzie nasza systematyczna metoda dowodzenia nielegalności
    negatywnych typów induktywnych.

    Oczywiście oryginalne sformułowanie twierdzenia powstało na długo przed
    powstaniem teorii typów czy Coqa, co objawia się np. w tym, że mówi ono
    o _zbiorze_ liczb naturalnych, podczas gdy my dysponujemy _typem_ liczb
    naturalnych. Musimy więc oryginalne sformułowanie lekko przeformułować,
    a także wprowadzić wszystkie niezbędne nam pojęcia. *)

Definition surjective {A B : Type} (f : A -> B) : Prop :=
  forall b : B, exists a : A, f a = b.

(** Pierwszym niezbędnym pojęciem jest pojęcie surjekcji. Powyższa definicja
    głosi, że funkcja jest surjektywna, gdy każdy element przeciwdziedziny
    jest wynikiem funkcji dla pewnego elementu dziedziny. Surjekcja to
    funkcja, która jest surjektywna.

    O co chodzi w tej definicji? Samo słowo "surjekcja" pochodzi od fr.
    "sur" - "na" oraz łac. "iacere" - "rzucać". Ubogim tłumaczeniem na
    polski może być słowo "narzut".

    Idea jest taka, że surjekcja [f : A -> B] "narzuca" swoją dziedzinę
    [A] na przeciwdziedzinę [B] tak, że [A] "pokrywa" całe [B]. Innymi
    słowy, każdy element [b : B] jest pokryty przez jakiś element [a : A],
    co wyraża równość [f a = b]. Oczywiście to [a] nie musi być unikalne -
    [b] może być pokrywane przez dużo różnych [a]. Jak widać, dokładnie to
    jest napisane w powyższej definicji.

    Mówiąc jeszcze prościej: jeżeli [f : A -> B] jest surjekcją, to typ
    [A] jest większy (a precyzyjniej mówiący, nie mniejszy) niż typ [B].
    Oczywiście nie znaczy to, że jeżeli [f] nie jest surjekcją, to typ
    [A] jest mniejszy niż [B] - mogą przecież istnieć inne surjekcje.
    Powiemy, że [A] jest mniejszy od [B], jeżeli nie istnieje żadna
    surjekcja między nimi.

    Spróbujmy rozrysować to niczym Jacek Gmoch... albo nie, bo nie umiem
    jeszcze rysować, więc zamiast tego będzie przykład i ćwiczenie. *)

Definition isZero (n : nat) : bool :=
match n with
| 0 => true
| _ => false
end.

Lemma surjective_isZero : surjective isZero.
Proof.
  unfold surjective. destruct b.
    exists 0. cbn. reflexivity.
    exists 42. cbn. reflexivity.
Qed.

(** Funkcja [isZero], która sprawdza, czy jej argument jest zerem, jest
    surjekcją, bo każdy element typu [bool] może być jej wynikiem -
    [true] jest wynikiem dla [0], zaś [false] jest jej wynikiem dla
    wszystkich innych argumentów. Wobec tego możemy skonkludować, że
    typ [nat] jest większy niż typ [bool] i w rzeczywistości faktycznie
    tak jest: [bool] ma dwa elementy, a [nat] nieskończenie wiele.

    Do kwestii tego, który typ ma ile elementów wrócimy jeszcze w rozdziale
    o typach i funkcjach. Tam też zapoznamy się lepiej z surjekcjami i
    innymi rodzajami funkcji. Tymczasem: *)

(** **** Ćwiczenie *)

(** Czy funkcja [plus 5] jest surjekcją? A funkcja [fun n : nat => minus n 5]?
    Sprawdź swoje odpowiedzi w Coqu. Na koniec filozoficznie zinterpretuj
    otrzymany wynik.

    Wskazówka: [minus] to funkcja z biblioteki standardowej, która
    implementuje odejmowanie liczb naturalnych z obcięciem, czyli np.
    [2 - 5 = 0]. Użyj [Print]a, żeby dokładnie zbadać jej definicję. *)

(* begin hide *)
(* Jest oczywiste, że [+ 5] nie jest surjekcją, zaś [- 5] tak. *)
(* end hide *)

(** Pozostaje jeszcze kwestia tego, czym jest "zbiór potęgowy zbioru liczb
    naturalnych". Mimo groźnej nazwy sprawa jest prosta: jest to archaiczne
    określenie na typ funkcji [nat -> bool]. Każdą funkcję [f : nat -> bool]
    możemy interpretować jako pewną kolekcję (czyli właśnie zbiór) elementów
    typu [nat], zaś [f n], czyli wynik [f] na konkretnym [n], mówi nam, czy
    [n] znajduje się w tej kolekcji, czy nie.

    To w zasadzie wyczerpuje zestaw pojęć potrzebnych nam do sformułowania
    twierdzenia. Pojawiająca się w oryginalnej wersji "większa moc" to po
    prostu synonim określenia "większy", które potrafimy już wyrażać za
    pomocą pojęcia surjekcji. Tak więc nowszą (czyli bardziej postępową)
    wersję twierdzenia Cantora możemy sformułować następująco: nie istnieje
    surjekcja z [nat] w [nat -> bool]. Lub jeszcze bardziej obrazowo: [nat]
    jest mniejsze niż [nat -> bool]. *)

Lemma Cantor :
  forall f : nat -> (nat -> bool), ~ surjective f.
Proof.
  unfold surjective. intros f Hf.
  pose (diagonal := fun n : nat => negb (f n n)).
  destruct (Hf diagonal) as [n Hn].
  apply (f_equal (fun h : nat -> bool => h n)) in Hn.
  unfold diagonal in Hn. destruct (f n n); inversion Hn.
Qed.

(* begin hide *)
(* TODO: konstruktywizacja twierdzenia kantora *)
Lemma Cantor_constructive :
  forall f : nat -> (nat -> bool),
    exists g : nat -> bool,
      forall n : nat, f n <> g.
Proof.
  intro f.
  exists (fun n : nat => negb (f n n)).
  intros n Heq.
  apply (f_equal (fun f => f n)) in Heq.
  destruct (f n n); inversion Heq.
Qed.
(* end hide *)

(** Dowód twierdzenia jest równie legendarny jak samo twierdzenie, a na
    dodatek bajecznie prosty i niesamowicie użyteczny - jeżeli będziesz
    zajmował się w życiu matematyką i informatyką, spotkasz go w jeszcze
    wielu odsłonach. Metoda stojąca za dowodem nazywana bywa argumentem
    przekątniowym - choć nazwa ta może się wydawać dziwna, to za chwilę
    stanie się zupełnia jasna.

    O co więc chodzi w powyższym dowodzie? Po pierwsze zauważmy, że
    mamy do czynienia z funkcją [f : nat -> (nat -> bool)], czyli
    funkcją, która bierze liczbę naturalną i zwraca funkcję z liczb
    naturalnych w [bool]. Pamiętajmy jednak, że [->] łączy w prawo
    i wobec tego typ [f] możemy zapisać też jako [nat -> nat -> bool].
    Tak więc [f] jest funkcją, która bierze dwie liczby naturalne i
    zwraca element typu [bool].

    Dzięki temu zabiegowi możemy wyobrażać sobie [f] jako dwuwymiarową
    tabelkę, której wiersze i kolumny są indeksowane liczbami naturalnymi,
    a komórki w tabelce wypełnione są wartościami typu [bool]. Przyjmijmy,
    że pierwszy argument [f] to indeks wiersza, zaś drugi to indeks kolumny.
    W takim układzie [f n m] to wartość [n]-tej funkcji na argumencie [m].
    Wobec tego twierdzenie możemy sparafrazować mówiąc, że każda funkcja
    [nat -> bool] znajduje się w którymś wierszu tabelki.

    To tyle wyobraźni - możemy już udowodnić twierdzenie. Na początku
    oczywiście bierzemy dowolne [f] oraz zakładamy, że jest surjekcją,
    uprzednio odwijając definicję bycia surjekcją.

    Teraz musimy jakoś wyciągnąć sprzeczność z hipotezy [Hf], czyli,
    używając naszej tabelkowej parafrazy, znaleźć funkcję z [nat] w
    [bool], która nie znajduje się w tabelce. A nie znajdować się w
    tabelce, panie Ferdku, to znaczy: różnić się od każdej funkcji z
    tabelki na jakimś argumencie.

    Zamiast jednak szukać takiej funkcji po omacku, skonstruujmy ją
    z tego, co mamy pod ręką - czyli z naszej tabelki. Jak przerobić
    funkcje z tabelki na nową, której w nie ma w tabelce? Tu właśnie
    ujawnia się geniuszalność Cantora: użyjemy metody przekątniowej,
    czyli spojrzymy na przekątną naszej tabelki.

    Definiujemy więc nową funkcję [diagonal : nat -> bool] następująco:
    dla argumentu [n : nat] bierzemy funkcję z [n]-tego wiersza w tabelce,
    patrzymy na [n]-tą kolumnę, czyli na wartość funkcji na argumencie
    [n], i zwracamy negację tego, co tam znajdziemy. Czujesz sprzeczność?

    Nasze założenie mówi, że [diagonal] znajduje się w którymś wierszu
    tabelki - niech ma on numer [n]. Wiemy jednak, że [diagonal] różni
    się od [n]-tej funkcji z tabelki na argumencie [n], gdyż zdefiniowaliśmy
    [diagonal n] jako negację tej właśnie komórki w tabelce. Dostajemy stąd
    równość [f n n = diagonal n = negb (f n n)], co po analizie przypadków daje
    ostatecznie [true = false] lub [false = true].

    Voilà! Sprzeczność osiągnięta, a zatem początkowe założenie było
    błędne i nie istnieje żadna surjekcja z [nat] w [nat -> bool]. *)

(** **** Ćwiczenie *)

(** Udowodnij, że nie ma surjekcji z [nat] w [nat -> nat]. Czy jest surjekcja
    z [nat -> bool] w [(nat -> bool) -> bool]? A w [nat -> bool -> bool]? *)

(** Poznawszy twierdzenie Cantora, możemy powrócić do ścisłej pozytywności,
    czyż nie? Otóż nie, bo twierdzenie Cantora jest biedne. Żeby móc czerpać
    z niego niebotyczne profity, musimy najpierw uogólnić je na dowolne
    dwa typy [A] i [B] znajdując kryterium mówiące, kiedy nie istnieje
    surjekcja z [A] w [A -> B]. *)

Lemma Cantor' :
  forall
    {A B : Type}
    (f : A -> (A -> B))
    (modify : B -> B)
    (H : forall b : B, modify b <> b),
      ~ surjective f.
Proof.
  unfold surjective. intros A B f modify H Hf.
  pose (g := fun x : A => modify (f x x)).
  destruct (Hf g) as [x Hx].
  apply (f_equal (fun h => h x)) in Hx.
  unfold g in Hx. apply (H (f x x)).
  symmetry. assumption.
Qed.

(** Uogólnienie jest dość banalne. Najpierw zastępujemy [nat] i [bool] przez
    dowolne typy [A] i [B]. W oryginalnym twierdzeniu nie użyliśmy żadnej
    właściwości liczb naturalnych, więc nie musimy szukać żadnych kryteriów
    dla typu [A]. Nasza tabelka może równie dobrze być indeksowana elementami
    dowolnego typu - dalej jest to tabelka i dalej ma przekątną.

    Twierdzenie było jednak zależne od pewnej właściwości [bool], mianowicie
    funkcja [diagonal] była zdefiniowana jako negacja przekątnej. Było nam
    jednak potrzeba po prostu funkcji, która dla każdego elementu z przekątnej
    zwraca element [bool] od niego różny. Ponieważ [bool] ma dokładnie dwa
    elementy, to negacja jest jedyną taką funkcją.

    Jednak w ogólnym przypadku dobra będzie dowolna [B]-endofunkcja bez
    punktów stałych. Ha! Nagły atak żargonu bezzębnych ryb, co? Zróbmy
    krótką przerwę, żeby zbadać sposób komunikacji tych czarodziejskich
    zwierząt pływających po uczelnianych korytarzach.

    Endofunkcja to funkcja, która ma taką samą dziedzinę i przeciwdziedzinę.
    Można się zatem domyślać, że [B]-endofunkcja to funkcja o typie [B -> B].
    Punkt stały zaś to takie [x], że [f x = x]. Jest to więc dokładnie ta
    własność, której chcemy, żeby pożądana przez nas funkcja nie miała dla
    żadnego [x]. Jak widać, żargon bezzębnych ryb jest równie zwięzły jak
    niepenetrowalny dla zwykłych śmiertelników.

    Podsumowując: w uogólnionym twierdzeniu Cantora nie wymagamy niczego od
    [A], zaś od [B] wymagamy tylko, żeby istniała funkcja [modify : B -> B],
    która spełnia [forall b : B, modify b <> b]. Dowód twierdzenia jest taki
    jak poprzednio, przy czym zastępujemy użycie [negb] przez [modify]. *)

(** **** Ćwiczenie *)

(** Znajdź jedyny słuszny typ [B], dla którego nie istnieje żadna
    [B]-endofunkcja bez punktów stałych.

    Podpowiedź: to zadanie jest naprawdę proste i naprawdę istnieje jedyny
    słuszny typ o tej właściwości.

    Pytanie (bardzo trudne): czy da się udowodnić w Coqu, że istnieje
    dokładnie jeden taki typ? Jeżeli tak, to w jakim sensie typ ten
    jest unikalny i jakich aksjomatów potrzeba do przepchnięcia dowodu? *)

(* begin hide *)

Lemma unit_unique_type_without_endofunction_without_fixpoints :
  (forall {A : Type} (x y : A), {x = y} + {x <> y}) ->
  forall A : Type,
    (forall f : A -> A, exists x : A, f x = x) ->
      exists (f : A -> unit) (g : unit -> A),
        (forall x : A, g (f x) = x).
Proof.
  intros K A H.
  destruct (H (fun x : A => x)) as [x eq].
  exists (fun _ => tt), (fun _ => x).
  intro y.
  pose (f := fun a : A =>
    match K A a x with
    | left _ => y
    | _ => x
    end).
  specialize (H f).
  destruct H as [z H].
  unfold f in H.
  destruct (K A z x); congruence.
Qed.

(* end hide *)

(** * Twierdzenie Cantora jako młot na negatywność *)

(** Z Cantorem po naszej stronie możemy wreszcie kupić ruble... ekhem,
    możemy wreszcie zaprezentować ogólną metodę dowodzenia, że negatywne
    typy induktywne prowadzą do sprzeczności. Mimo szumnej nazwy ogólna
    metoda nie jest aż taka ogólna i czasem będziemy musieli się bonusowo
    napracować. *)

Module Example1.

(** Otworzymy sobie nowy moduł, żeby nie zaśmiecać globalnej przestrzeni
    nazw - wszystkie nasze złe typy będą się nazywały [wut]. Przy okazji,
    zdecydowanie powinieneś nabrać podejrzeń do tej nazwy - jeżeli coś w
    tej książce nazywa się [wut], to musi to być złowrogie, podejrzane
    paskudztwo. *)

Unset Positivity Checking.
Inductive wut (A : Type) : Type :=
| C : (wut A -> A) -> wut A.
Set Positivity Checking.

Arguments C {A} _.

(** Podobnie jak poprzednio, żeby Coq pozwolił nam zdefiniować [wut] musimy
    na czas definicji wyłączyć sprawdzanie kryterium ścisłej pozytywności.
    Dlaczego bez wykonania tego zabiegu typ [wut A] jest nielegalny, a jego
    definicja zostałaby przez Coqa odrzucona? Poza wspomnianymi w poprzednim
    podrozdziale problemami filozoficznymi wynikającymi z nieterminacji,
    jest też drugi, bardziej namacalny powód: istnienie typu [wut A] jest
    sprzeczne z (uogólnionym) twierdzeniem Cantora. *)

Definition extract {A : Type} (w : wut A) : wut A -> A :=
match w with
| C f => f
end.

(** Powód tej sprzeczności jest dość prozaiczny: za pomocą konstruktora [C]
    możemy z dowolnej funkcji [wut A -> A] zrobić element [wut A], a skoro
    tak, to dowolny element typu [wut A] możemy odpakować i wyjąć z niego
    funkcję o typie [wut A -> A]. *)

Lemma surjective_extract :
  forall A : Type, surjective (@extract A).
Proof.
  unfold surjective.
  intros A f.
  exists (C f).
  cbn. reflexivity.
Qed.

(** Skoro możemy włożyć dowolną funkcję, to znaczy, że dla każdej funkcji
    istnieje element, z którego możemy ją wyjąć, a zatem mamy do czynienia
    z surjekcją. *)

Lemma wut_illegal : False.
Proof.
  apply (Cantor' (@extract bool) negb).
    destruct b; inversion 1.
    apply surjective_extract.
Qed.

(** W połączeniu zaś z twierdzeniem Cantora surjekcja [wut A -> (wut A -> A)]
    prowadzi do sprzeczności - wystarczy za [A] wstawić [bool]. *)

End Example1.

(** Przykład może ci się jednak wydać niezadowalający - typ [wut] jest
    przecież dość nietypowy, bo ma tylko jeden konstruktor. A co, gdy
    konstruktorów jest więcej?

    Początkowo miałem opisać kilka przypadków z większą liczbą konstruktorów,
    ale stwierdziłem, że jednak mi się nie chce. W ćwiczeniach zobaczymy, czy
    będziesz w stanie sam wykombinować, jak się z nimi uporać (wskazówka: jest
    to bardzo łatwe, wystarczy chcieć i nie być leniwym jak ja). *)

(** **** Ćwiczenie *)

(** Poniższe paskudztwo łamie prawo ścisłej pozytywności nie jednym, lecz
    aż dwoma swoimi konstruktorami. Udowodnij, że jego istnienie prowadzi
    do sprzeczności. Metoda jest podobna jak w naszym przykładzie, ale
    trzeba ją troszkę dostosować do zastanej sytuacji. *)

Module Exercise1.

Unset Positivity Checking.
Inductive wut : Type :=
| C0 : (wut -> bool) -> wut
| C1 : (wut -> nat) -> wut.
Set Positivity Checking.

(* begin hide *)
Definition extract (w : wut) : wut -> bool :=
match w with
| C0 f => f
| C1 _ => fun _ => true
end.

Lemma surjective_extract :
  surjective extract.
Proof.
  red. intros.
  exists (C0 b).
  reflexivity.
Qed.
(* end hide *)

Lemma wut_illegal : False.
(* begin hide *)
Proof.
  apply (Cantor' extract negb).
    destruct b; inversion 1.
    apply surjective_extract.
Qed.
(* end hide *)

End Exercise1.

(** **** Ćwiczenie *)

(** Poniższe paskudztwo ma jeden konstruktor negatywny, a drugi pozytywny,
    niczym typowa panienka z borderlajnem...

    Polecenie jak w poprzednim ćwiczeniu. *)

Module Exercise2.

Unset Positivity Checking.
Inductive wut : Type :=
| C0 : (wut -> wut) -> wut
| C1 : nat -> wut.
Set Positivity Checking.

(* begin hide *)
Definition extract (w : wut) : wut -> wut :=
match w with
| C0 f => f
| C1 _ => id
end.

Lemma surjective_extract :
  surjective extract.
Proof.
  red. intros.
  exists (C0 b).
  reflexivity.
Qed.

Definition modify (w : wut) : wut :=
match w with
| C0 _ => C1 0
| C1 _ => C0 id
end.

Lemma modify_neq :
  forall w : wut, modify w <> w.
Proof.
  destruct w; inversion 1.
Qed.
(* end hide *)

Lemma wut_illegal : False.
(* begin hide *)
Proof.
  Check Cantor'.
  eapply (Cantor' extract modify).
    apply modify_neq.
    apply surjective_extract.
Qed.
(* end hide *)

End Exercise2.

(** **** Ćwiczenie *)

(** Poniższy typ reprezentuje termy beztypowego rachunku lambda, gdzie [V]
    to typ reprezentujący zmienne. Co to za zwierzątko ten rachunek lambda
    to my się jeszcze przekonamy... chyba, oby.

    Taki sposób reprezentowania rachunku lambda (i ogólnie składni języków
    programowania) nazywa się HOAS, co jest skrótem od ang. Higher Order
    Abstract Syntax. W wielu językach funkcyjnych jest to popularna technika,
    ale w Coqu, jak zaraz udowodnisz, jest ona nielegalna. Ława oburzonych
    jest rzecz jasna oburzona! *)

Module Exercise3.

Unset Positivity Checking.
Inductive Term (V : Type) : Type :=
| Var : V -> Term V
| Lam : (Term V -> Term V) -> Term V
| App : Term V -> Term V -> Term V.
Set Positivity Checking.

Arguments Var {V} _.
Arguments Lam {V} _.
Arguments App {V} _ _.

(* begin hide *)
Definition extract {V : Type} (t : Term V) : Term V -> Term V :=
match t with
| Var v => id
| Lam f => f
| App _ _ => id
end.

Lemma surjective_extract :
  forall {V : Type}, surjective (@extract V).
Proof.
  red. intros.
  exists (Lam b).
  cbn. reflexivity.
Qed.

Definition modify {V : Type} (t : Term V) : Term V :=
match t with
| Var _ => Lam id
| Lam f => App (Lam f) (Lam f)
| App _ _ => Lam id
end.

Lemma modify_neq :
  forall {V : Type} (t : Term V),
    modify t <> t.
Proof.
  destruct t; inversion 1.
Qed.
(* end hide *)

Lemma Term_illegal : False.
(* begin hide *)
Proof.
  eapply (Cantor' (@extract unit)). Unshelve. all: cycle 1.
    apply surjective_extract.
    apply modify.
    apply modify_neq.
Qed.
(* end hide *)

End Exercise3.

(** **** Ćwiczenie *)

(** Poniższe bydle jeszcze do niedawna wydawało mi się całkiem trudne i problematyczne,
    ale oczywiście jest bardzo proste. Uszy do góry i do dzieła! *)

Module Exercise4.

Unset Positivity Checking.
Inductive wut : Type :=
| C : (wut -> wut) -> wut.
Set Positivity Checking.

(* begin hide *)
Definition extract :
  wut -> (wut -> wut).
Proof.
  destruct 1 as [f].
  assumption.
Defined.

Lemma surjective_extract :
  surjective extract.
Proof.
  unfold surjective.
  intro f.
  exists (C f).
  cbn. reflexivity.
Qed.

Definition modify : wut -> wut :=
  fun w : wut => C (fun _ => w).

Lemma modify_neq :
  forall w : wut, modify w <> w.
Proof.
  fix IH 1.
  unfold modify in *.
  destruct w as [f].
  inversion 1.
  specialize (IH (f (C f))).
  rewrite <- H1 in IH.
  contradiction.
Qed.
(* end hide *)

Lemma wut_illegal : False.
(* begin hide *)
Proof.
  apply (Cantor' extract modify).
    apply modify_neq.
    apply surjective_extract.
Qed.
(* end hide *)

End Exercise4.

(** * Poradnik rozpoznawania negatywnych typów induktywnych *)

(** Skoro już wiemy, że negatywne typy induktywne są wynalazkiem szatana,
    to czas podać proste kryterium na ich rozpoznawanie. Jeżeli jesteś
    sprytny, to pewnie sam zdążyłeś już zauważyć ogólną regułę. Jednak aby
    nie dyskryminować osób mało sprytnych, trzeba napisać ją wprost.

    Kryterium jest banalne. Mając dany typ [T] musimy rzucić okiem na jego
    konstruktory, a konkretniej na ich argumenty. Argumenty nieindukcyjne
    (czyli o typach, w których nie występuje [T]) są zupełnie niegroźne i
    wobec tego powinniśmy je zignorować. Interesować nas będą wyłącznie
    argumenty indukcyjne, czyli takie, w których występuje typ [T].

    Najbardziej podstawowy typ argumentu indukcyjnego, czyli samo [T], jest
    rzecz jasna niegroźny. To samo dotyczy argumentu indukcyjnego o typie
    [nat -> T]. Wprawdzie jest on typu funkcyjnego, co, jak się zaraz przekonamy,
    jest groźne, ale [T] występuje po prawej stronie strzałki, więc wszystko jest
    w porządku. W ogólności w porządku są też argumenty typu [A -> T], gdzie [A]
    jest znanym typem niezależącym od [T].

    Niektóre typy argumentów indukcyjnych również są niegroźne, np. [T * T],
    [T + T], [list T] albo [{t : T | P t}], ale ich użycie sprawia, że Coq nie
    potrafi wygenerować dla definiowanego typu odpowiedniej reguły indukcji,
    więc generuje jedynie regułę analizy przypadków. Te typy argumentów nie
    prowadzą do sprzeczności, ale powinniśmy ich unikać, bo są upierdliwe i
    każde takie wystąpienie argumentu indukcyjnego można łatwo zrefaktoryzować.

    Argument typu [T * T] można zastąpić dwoma argumentami typu [T]
    i podobnie dla [{t : T | P t}]. Konstruktor z argumentem typu [T + T]
    możemy rozbić na dwa konstruktory (i powinniśmy, bo jest to bardziej
    czytelne). Konstruktor z wystąpieniem [list T] możemy przerobić na
    definicję przez indukcję wzajemną (ćwiczenie: sprawdź jak), ale lepiej
    chyba po prostu zaimplementować regułę indukcji ręcznie. *)

Inductive T0 : Type :=
| c0 : T0
| c1 : nat -> T0
| c2 : T0 -> T0
| c3 : nat * T0 -> T0
| c4 : T0 * T0 -> T0
| c5 : T0 + T0 -> T0
| c6 : list T0 -> T0
| c7 : (nat -> T0) -> T0.

(** Rodzaje nieszkodliwych typów argumentów widać na powyższym przykładzie.
    Konstruktory [c0] i [c1] są nieindukcyjne, więc są ok. Konstruktor [c2]
    jest indukcyjny - jest jeden argument typu [T0]. Zauważ, że typem
    konstruktora [c2] jest [T0 -> T0], ale nie oznacza to, że [T0]
    występuje po lewej stronie strzałki!

    Jest tak, gdyż ostatnie wystąpienie [T0] jest konkluzją konstruktora
    [c2]. Ważne są tylko wystąpienia po lewej stronie strzałki w argumentach
    (gdyby konstruktor [c2] nie był legalny, to jedynymi legalnymi typami
    induktywnymi byłyby enumeracje).

    Konstruktory [c3], [c4], [c5] i [c6] są induktywne i również w pełni
    legalne, ale są one powodem tego, że Coq nie generuje dla [T0] reguły
    indukcji, a jedynie regułę analizy przypadków (choć nazywa się ona
    [T0_ind]). Konstruktor [c7] również jest w pełni legalny. *)

(** **** Ćwiczenie *)

(** Zrefaktoryzuj powyższy upośledzony typ. *)

(* begin hide *)
Inductive T0' : Type :=
| c0' : T0'
| c1' : nat -> T0'
| c2' : T0' -> T0'
| c3' : nat -> T0' -> T0'
| c4' : T0' -> T0' -> T0'
| c51 : T0' -> T0'
| c52 : T0' -> T0'
| c6' : List_T0' -> T0'
| c7' : (nat -> T0') -> T0'

with List_T0' : Type :=
| T0'_nil  : List_T0'
| T0'_cons : T0' -> List_T0' -> List_T0'.
(* end hide *)

(** Problem pojawia się dopiero wtedy, gdy typ [T] występuje po lewej
    stronie strzałki, np. [T -> bool], [T -> T], [(T -> T) -> T], lub
    gdy jest skwantyfikowany uniwersalnie, np. [forall t : T, P t] (typ
    [T] jest dziedziną kwantyfikacji) lub [forall f : (forall t : T, P t), Q f]
    (tym razem [T] jest dziedziną dziedziny kwantyfikacji).

    W trzech poprzednich podrozdziałach mierzyliśmy się z sytuacjami, gdy
    typ [T] występował bezpośrednio na lewo od strzałki, ale oczywiście
    może on być dowolnie zagnieżdżony. Dla każdego wystąpienia [T] w
    argumentach możemy policzyć, na lewo od ilu strzałek się ono znajduje
    (czyli jak mocno zagnieżdżona jest dziedzina kwantyfikacji). Liczbę tę
    nazywać będziemy niedobrością. W zależności od niedobrości,
    wystąpienie nazywamy:
    - 0 - wystąpienie ściśle pozytywne
    - liczba nieparzysta - wystąpienie negatywne
    - liczba parzysta (poza 0) - wystąpienie pozytywne

    Jeżeli w definicji mamy wystąpienie negatywne, to typ możemy nazywać
    negatywnym typem induktywnym (choć oczywiście nie jest to legalny typ
    induktywny). Jeżeli nie ma wystąpień negatywnych, ale są wystąpienia
    pozytywne, to typ nazywamy pozytywnym typem induktywnym (lub
    nie-ściśle-pozytywnym typem induktywnym), choć oczywiście również nie
    jest to legalny typ induktywny. Jeżeli wszystkie wystąpienia są ściśle
    pozytywne, to mamy do czynienia po prostu z typem induktywnym.
    Parafrazując: każdy typ induktywny jest ściśle pozytywny.

    Podobne nazewnictwo możemy sobie wprowadzić dla konstruktorów
    (konstruktory negatywne, pozytywne i ściśle pozytywne), ale nie
    ma sensu, bo za tydzień i tak zapomnisz o tych mało istotnych detalach.
    Ważne, żebyś zapamiętał najważniejsze, czyli ideę. *)

(*
Inductive T1 : Type :=
| T1_0 : T1 -> T1
| T1_1 : (T1 -> T1) -> T1
| T1_2 : ((T1 -> T1) -> T1) -> T1
| T1_3 : forall (t : T1) (P : T1 -> Prop), P t -> T1.
*)

(** W powyższym przykładzie wystąpienie [T1] w pierwszym argumencie
    [T1_0] jest ściśle pozytywne (na lewo od 0 strzałek). Pierwsze
    wystąpienie [T1] w [T1_1] jest negatywne (na lewo od 1 strzałki),
    a drugie ściśle pozytywne (na lewo od 0 strzałek). Pierwsze
    wystąpienie [T1] w [T1_2] jest pozytywne (na lewo od 2 strzałek),
    drugie negatywne (na lewo od 1 strzałki), trzecie zaś ściśle
    pozytywne (na lewo od 0 strzałek). Pierwsze wystąpienie [T1] w
    [T1_3] jest negatywne (dziedzina kwantyfikacji), drugie zaś
    pozytywne (na lewo od jednej strzałki, ale ta strzałka jest w
    typie, po którym kwantyfikujemy).

    Konstruktor [T1_0] jest ściśle pozytywny, zaś konstruktory [T1_1],
    [T1_2] oraz [T1_3] są negatywne. Wobec tego typ [T1] jest negatywnym
    typem induktywnym (czyli nie jest legalnym typem induktywnym i dlatego
    właśnie Coq odrzuca jego definicję). *)

(** **** Ćwiczenie *)

(*
Inductive T2 : Type :=
| T2_0 :
    forall f : (forall g : (forall t : T2, nat), Prop), T2
| T2_1 :
    (((((T2 -> T2) -> T2) -> T2) -> T2) -> T2) -> T2
| T2_2 :
  ((forall (n : nat) (P : T2 -> Prop),
    (forall t : T2, nat)) -> T2) -> T2 -> T2 -> T2.
*)

(** Policz niedobrość każdego wystąpienia [T2] w powyższej definicji.
    Sklasyfikuj konstruktory jako negatywne, pozytywne lub ściśle
    pozytywne. Następnie sklasyfikuj sam typ jako negatywny, pozytywny
    lub ściśle pozytywny. *)

(** **** Ćwiczenie *)

(* Inductive T : Type := *)

(** Rozstrzygnij, czy następujące konstruktory spełniają kryterium ścisłej
    pozytywności. Jeżeli tak, narysuj wesołego jeża. Jeżeli nie, napisz
    zapętlającą się funkcję podobną do [loop] (zakładamy, że typ [T] ma
    tylko ten jeden konstruktor). Następnie sprawdź w Coqu, czy udzieliłeś
    poprawnej odpowiedzi.
    - [| C1 : T]
    - [| C2 : bool -> T]
    - [| C3 : T -> T]
    - [| C4 : T -> nat -> T]
    - [| C5 : forall A : Type, T -> A -> T]
    - [| C6 : forall A : Type, A -> T -> T]
    - [| C7 : forall A : Type, (A -> T) -> T]
    - [| C8 : forall A : Type, (T -> A) -> T]
    - [| C9 : (forall x : T, T) -> T]
    - [| C10 : (forall (A : Type) (x : T), A) -> T]
    - [| C11 : forall A B C : Type,
                  A -> (forall x : T, B) -> (C -> T) -> T] *)

(* begin hide *)
(* C1-C7 są legalne, C8-C11 nie. *)
(* end hide *)

(** * Kilka bonusowych pułapek *)

(** Wiemy już, że niektóre typy argumentów indukcyjnych są ok ([T], [A -> T]),
    inne problematyczne ([T * T], [list T]), a jeszcze inne nielegalne ([T -> T],
    [forall t : T, ...]). Uważny i żądny wiedzy czytelnik (daj boże, żeby tacy
    istnieli) zeche zapewne postawić sobie pytanie: które dokładnie typy argumentów
    indukcyjnych są ok, a które są wynalazkiem szatana? *)

(** ** Zabawy z parametrami *)

(** Najprościej będzie sprawę zbadać empirycznie, czyli na przykładzie.
    Żeby zaś przykład był reprezentatywny, niech parametrem definicji
    będzie dowolna funkcja [F : Type -> Type]. *)

Fail Inductive wut (F : Type -> Type) : Type :=
| wut_0 : F (wut F) -> wut F.
(* ===> The command has indeed failed with message:
        Non strictly positive occurrence of "wut" in
        "F (wut F) -> wut F". *)

(** Jak widać, jeżeli zaaplikujemy [F] do argumentu indukcyjnego, to Coq
    krzyczy, że to wystąpienie nie jest ściśle pozytywne. Dlaczego tak
    jest, skoro [F] nie jest ani strzałką, ani kwantyfikatorem uniwersalnym?
    Dlatego, że choć nie jest nimi, to może nimi zostać. Jeżeli zdefiniujemy
    sobie gdzieś na boku [F := fun A : Type => A -> bool], to wtedy
    [wut_0 F : (wut F -> bool) -> wut F], a z takim diabelstwem już się
    mierzyliśmy i wiemy, że nie wróży ono niczego dobrego.

    Morał z tej historii jest dość banalny: gdy definiujemy typ induktywny
    [T], jedynymi prawilnymi typami dla argumentu indukcyjnego są [T] oraz
    typy funkcji, które mają [T] jako konkluzję ([A -> T], [A -> B -> T]
    etc.). Wszystkie inne albo rodzą problemy z automatyczną generacją
    reguł indukcji ([T * T], [list T]), albo prowadzą do sprzeczności
    ([T -> T], [forall t : T, ...]), albo mogą prowadzić do sprzeczności,
    jeżeli wstawi się za nie coś niedobrego ([F T]). *)

(** **** Ćwiczenie *)

(** Zdefiniuj rodzinę typów z powyższego przykładu (wyłączając sprawdzanie
    kryterium ścisłej pozytywności) i udowodnij, że jej istnienie prowadzi
    do sprzeczności. *)

(* begin hide *)
Module wutF.

Unset Positivity Checking.
Inductive wut (F : Type -> Type) : Type :=
| wut_0 : F (wut F) -> wut F.
Set Positivity Checking.

Definition F (A : Type) : Type := A -> bool.

Definition extract (w : wut F) : wut F -> bool :=
match w with
| wut_0 _ f => f
end.

Lemma surjective_extract :
  surjective extract.
Proof.
  red. intros.
  exists (wut_0 _ b).
  cbn. reflexivity.
Qed.

Lemma extract_not_sur :
  ~ surjective extract.
Proof.
  unfold surjective. intro H.
  destruct (H (fun w : wut F => negb (extract w w))) as [w eq].
  apply (f_equal (fun f => f w)) in eq.
  destruct (extract w w); inversion eq.
Qed.

Lemma wut_illegal : False.
Proof.
  apply extract_not_sur. apply surjective_extract.
Qed.

End wutF.
(* end hide *)

(** ** Pułapki dla indukcji wzajemnej *)

(** To jeszcze nie koniec wrażeń na dziś - póki co omówiliśmy wszakże
    kryterium ścisłej pozytywności jedynie dla bardzo prostych typów
    induktywnych. Słowem nie zająknęliśmy się nawet na temat typów
    wzajemnie induktywnych czy indeksowanych typów induktywnych. Nie
    trudno będzie nam jednak uzupełnić naszą wiedzę, gdyż w przypadku
    oby tych mechanizmów kryterium ścisłej pozytywności wygląda podobnie
    jak w znanych nam już przypadkach (choć jest kilka kruczków, na które
    trzeba uważać). Spójrzmy na poniższy przykład: *)

Fail Inductive X : Type :=
| X0 : X
| X1 : (Y -> X) -> X

with Y : Type :=
| Y0 : Y
| Y1 : X -> Y.

(* ===> The command has indeed failed with message:
        Non strictly positive occurrence of "Y"
        in "(Y -> X) -> X". *)

(** Jak widać, powyższa definicja [X] i [Y] przez wzajemną indukcję jest
    nielegalna, gdyż jedyny argument konstruktora [X1] ma typ [Y -> X].
    Mogłoby wydawać się, że wszystko jest w porządku, wszakże [X] występuje
    tutaj na pozycji ściśle pozytywnej. Jednak ponieważ jest to definicja
    przez indukcję wzajemną, kryterium ścisłej pozytywności stosuje się nie
    tylko do wystąpień [X], ale także do wystąpień [Y] - wszystkie wystąpienia
    [X] oraz [Y] muszą być ściśle pozytywne zarówno w konstruktorach typu [X],
    jak i w konstruktorach typu [Y]. *)

(** **** Ćwiczenie *)

(** Zdefiniuj typy [X] i [Y] wyłączając positivity checker. Udowodnij za
    pomocą twierdzenia Cantora, że typy [X] i [Y] są nielegalne. Zdefiniuj
    też nieterminujące elementy [loopx : X] oraz [loopy : Y] i pobaw się
    nimi w trybie dowodzenia, żeby upewnić się, że faktyzcnie nie terminują.
    Pytanie bonusowe: czy do zdefiniowania [loopx] i [loopy] konieczna jest
    rekursja wzajemna? *)

(* begin hide *)
Require Import FunctionalExtensionality.

Module XY.

Unset Positivity Checking.
Inductive X : Type :=
| X0 : X
| X1 : (Y -> X) -> X

with Y : Type :=
| Y0 : Y
| Y1 : X -> Y.
Set Positivity Checking.

Definition extract (x : X) : X -> X :=
match x with
| X0 => id
| X1 f => fun x' : X => f (Y1 x')
end.

Lemma surjective_extract :
  surjective extract.
Proof.
  red. intro f.
  exists (X1 (fun y => match y with | Y0 => f X0 | Y1 x => f x end)).
  extensionality x.
  cbn. reflexivity.
Qed.

Definition modify (x : X) : X :=
match x with
| X0 => X1 (fun _ => x)
| X1 _ => X0
end.

Lemma modify_neq :
  forall x : X, modify x <> x.
Proof.
  destruct x; inversion 1.
Qed.

Lemma XY_illegal : False.
Proof.
  apply (Cantor' extract modify).
    apply modify_neq.
    apply surjective_extract.
Qed.

Definition loopx : X :=
  let
    f (y : Y) : X :=
      match y with
      | Y1 (X1 h) => h y
      | _         => X0
      end
  in
    f (Y1 (X1 f)).

Lemma loopx_nontermination :
  loopx = X0.
Proof.
  cbv delta [loopx] zeta.
  cbv beta. cbv iota.

  cbv beta. cbv iota.
  cbv beta. cbv iota.
Abort.

Definition loopy : Y := Y1 loopx.

Lemma loopy_nontermination :
  loopy = Y0.
Proof.
  cbv delta [loopy loopx] zeta.
  cbv beta. cbv iota.

  cbv beta. cbv iota.
  cbv beta. cbv iota.
Abort.

End XY.
(* end hide *)

(** * Jeszcze więcej pułapek *)

(** To już prawie koniec naszej wędrówki przez świat nielegalnych typów
    "induktywnych". Dowiedzieliśmy się, że negatywne typy induktywne
    prowadzą do nieterminacji i nauczyliśmy się wykorzystywać twierdzenie
    Cantora do dowodzenia nielegalności takich typów.

    Poznaliśmy też jednak klasyfikację typów wyglądających na induktywne
    (ściśle pozytywne, pozytywne, negatywne), a w szczególności pojęcie
    "niedobrości" indukcyjnego wystąpienia definiowanego typu w konstruktorze
    (upraszczając, na lewo od ilu strzałek znajduje się to wystąpienie).

    Piszę "jednak", gdyż z jej powodu możemy czuć pewien niedosyt - wszystkie
    dotychczasowe przykłady były typami negatywnymi o niedobrości równej 1.
    Podczas naszej intelektualnej wędrówki zwiedziliśmy mniej miejscówek,
    niż moglibyśmy chcieć. W tym podrozdziale spróbujemy ten przykry niedosyt
    załatać, rozważając (nie ściśle) pozytywne typy induktywne. Zobaczymy
    formalny dowód na to, że nie są one legalne (lub, precyzyjniej pisząc,
    dowód na to, że conajmniej jeden z nich nie jest legalny). Zanim jednak
    to się stanie, zobaczmy, czy wypracowane przez nas techniki działają na
    negatywne typy induktywne o niedobrości innej niż 1. *)

(** ** Większa niedobrość *)

Module T3.

Unset Positivity Checking.
Inductive T3 : Type :=
| T3_0 : (((T3 -> bool) -> bool) -> bool) -> T3.
Set Positivity Checking.

(** Przyjrzyjmy się powyższej definicji. Występienie indukcyjne typu [T3]
    ma współczynnik niedobrości równy 3, gdyż znajduje się na lewo od 3
    strzałek. Prawe strony wszystkich z nich to [bool]. Zanim zobaczymy,
    jak pokazać nielegalność tego typu metodą Cantora, przypomnijmy sobie
    pewien kluczowy fakt dotyczący negacji i jego banalne uogólnienie. *)

Lemma triple_negation :
  forall P : Prop, ~ ~ ~ P -> ~ P.
(* begin hide *)
Proof.
  intros P f x. apply f. intro g. apply g. exact x.
Qed.
(* end hide *)

Lemma triple_arrow :
  forall A B : Type, (((A -> B) -> B) -> B) -> (A -> B).
(* begin hide *)
Proof.
  intros A B f x. apply f. intro g. apply g. exact x.
Qed.
(* end hide *)

(** Fakt ten przypomina nam, że jeżeli chodzi o spamowanie negacją, to
    są w zasadzie tylko trzy sytuacje:
    - brak negacji
    - pojedyncza negacja
    - podwójna negacja

    Jeżeli mamy do czynienia z większą liczbą negacji, to możemy zdejmować
    po dwie aż dojdziemy do któregoś z powyższych przypadków. Ponieważ
    negacja to tylko implikacja, której kodziedziną jest [False], a nie
    korzystamy w dowodzie z żadnych specjalnych właściwości [False],
    analogiczna właściwość zachodzi także dla dowolnego innego [B : Type]. *)

Definition extract (x : T3) : T3 -> bool :=
match x with
| T3_0 f => fun y : T3 => f (fun g => g y)
end.

(** Wobec powyższych rozważań definicja funkcji [extract] zupełnie nie powinna
    cię zaskakiwać (a jeżeli cię zaskakuje, to sprawdź jak wygląda term, który
    skonstruowałeś dowodząc [triple_arrow] - jeżeli zrobiłeś to dobrze, to
    powinien wyglądać podobnie do definicji [extract]). Szczerze pisząc, reszta
    dowodu również nie jest jakoś specjalnie wymagająca czy oświecająca. *)

(** **** Ćwiczenie *)

(** Dokończ dowód. *)

Lemma surjective_extract :
  surjective extract.
(* begin hide *)
Proof.
  red. intro f.
  exists (T3_0 (fun g => g f)).
  cbn. reflexivity.
Qed.
(* end hide *)

Lemma T3_illegal : False.
(* begin hide *)
Proof.
  apply (Cantor' extract negb).
    destruct b; inversion 1.
    apply surjective_extract.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Napisanie zapętlającej się funkcji [loop : T3 -> bool] też nie
    jest jakoś wybitnie trudne. Napisz ją i pobaw się nią w trybie
    dowodzenia, żeby przekonać się, że faktycznie nie terminuje
    (dla jakiegoś argumentu [x : T3], który musisz sam wymyślić -
    to również nie jest specjalnie trudne). *)

(* begin hide *)
Definition loop (x : T3) : bool :=
match x with
| T3_0 f => f (fun g : T3 -> bool => g (T3_0 f))
end.

Definition bomb : T3 :=
  T3_0 (fun g => g loop).

Lemma loop_nontermination :
  loop bomb = true.
Proof.
  cbv delta [loop bomb].
  cbv beta. cbv iota.
  cbv beta. cbv iota.
Abort.
(* end hide *)

End T3.

(** Morał z powyższych rozważań jest prosty: nasze techniki działają także
    na negatywne typy induktywne o niedobrości równej 3. Myślę, że jesteś
    całkiem skłonny uwierzyć też, że zadziałają na te o niedobrości równej
    5, 7 i tak dalej. *)

(** ** Upierdliwe kodziedziny *)

Require Import FunctionalExtensionality.

(** To wszystko jest prawdą jednak tylko wtedy, gdy wszystkie typy po prawych
    stronach strzałek będą takie same. A co, gdy będą różne? *)

Module T4.

Unset Positivity Checking.
Inductive T4 : Type :=
| c0 : (((T4 -> bool) -> nat) -> Color) -> T4.
Set Positivity Checking.

(** Powyższy przykład jest podobny do poprzedniego, ale tym razem zamiast
    trzech wystąpień [bool] mamy [bool], [nat] oraz [Color] (to ostatnie
    to typ, który zdefiniowaliśmy na samym początku tego rozdziału, gdy
    uczyliśmy się o enumeracjach). *)

Definition extract (x : T4) : T4 -> bool.
Proof.
  destruct x as [f].
  intros y.
  apply (
    fun c : Color =>
    match c with
    | R => true
    | _ => false
    end).
  apply f.
  intro g.
  apply (fun b : bool => if b then 0 else 1).
  apply g.
  exact y.
Defined.

(** Nasz modus operandi będzie taki jak poprzednio: spróbujemy wyjąć z
    elementu [T4] funkcję typu [T4 -> bool]. W tym celu rozbijamy [x]
    i wprowadzamy [y : T4] do kontekstu.

    Tym razem nie możemy jednak bezpośrednio zaaplikować [f], gdyż jej
    kodziedziną jest [Color], a my musimy skonstruować coś typu [bool].
    Możemy temu jednak zaradzić aplikując do celu skonstruowaną naprędce
    funkcję typu [Color -> bool]. Ta funkcja powinna być surjekcją (jeśli
    nie wierzysz, sprawdź, co się stanie, jeżeli zamienimy ją na funckję
    stałą albo inną nie-surjekcję).

    Możemy już zaaplikować [f] i wprowadzić [g] do kontekstu. Chcielibyśmy
    teraz zaaplikować [g], ale nie możemy, bo typy się nie zgadzają - [g]
    zwraca [bool], a my musimy skonstruować liczbę naturalną. Robimy tutaj
    to samo co poprzednio - aplikujemy do celu jakąś funkcję [bool -> nat].
    Tym razem nie musi ona być surjekcją (nie jest to nawet możliwe, gdyż
    nie ma surjekcji z [bool] w [nat]). Dzięki temu możemy zaaplikować [g]
    i zakończyć, używając [y].

    Żeby pokazać, że [extract] jest surjekcją, będziemy potrzebować aksjomatu
    ekstensjonalności dla funkcji (ang. functional extensionality axiom,
    w skrócie funext). Głosi on, że dwie funkcje [f, g : A -> B] są równe,
    jeżeli uda nam się pokazać, że dają równe wyniki dla każdego argumentu
    (czyli [forall x : A, f x = g x]).

    Importując moduł [FunctionalExtensionality] zakładamy prawdziwość tego
    aksjomatu oraz uzyskujemy dostęp do taktyki [extensionality], która ułatwia
    dowody wymagające użycia ekstensjonalności. *)

Lemma surjective_extract :
  surjective extract.
Proof.
  unfold surjective, extract.
  intro f.
  exists (c0 (
    fun g : (T4 -> bool) -> nat =>
    match g f with
   | 0 => R
   | _ => G
    end)).
  extensionality y.
  destruct (f y); reflexivity.
Qed.

(** Dowód jest prawie taki jak zawsze: odwijamy definicję surjektywności i
    wprowadzamy hipotezy do kontekstu, a następnie odwijamy definicję [extract]
    i rozbijamy ją dla czytelności na właściwą funkcję [extract] oraz równanie
    [eq].

    Następnie musimy znaleźć [a : T4], które [extract] mapuje na [f]. Zaczynamy
    od [c0], bo jest to jedyny konstruktor [T4]. Bierze on jako argument
    funkcję typu [((T4 -> bool) -> nat) -> Color]. Żeby ją wyprodukować,
    bierzemy na wejściu funkcję [g : (T4 -> bool) -> nat] i musimy zrobić
    coś typu [Color].

    Nie może to być jednak byle co - musimy użyć [f], a jedynym sensownym
    sposobem, żeby to zrobić, jest zaaplikować [g] do [f]. Musimy zadbać
    też o to, żeby odwrócić funkcje konwertujące [Color -> bool] oraz
    [bool -> nat], których użyliśmy w definicji [extract]. Pierwsza z nich
    konwertowała [R] (czyli kolor czerwony) na [true], a inne kolory na
    [false], zaś druga konwertowała [true] na [0], a [false] na [1].
    Wobec tego dopasowując [g f : nat] musimy przekonwertować [0] na [R],
    zaś [1] na coś innego niż [R], np. na [G] (czyli kolor zielony).

    Znalazłszy odpowiedni argument, możemy przepisać równanie definiujące
    [extract]. To już prawie koniec, ale próba użycia taktyki [reflexivity] w
    tym momencie skończyłaby się porażką. Na ratunek przychodzi nam
    aksjomat ekstensjonalności, którego używamy pisząc [extensionality y].
    Dzięki temu pozostaje nam pokazać jedynie, że [f y] jest równe tej
    drugie funkcji dla argumentu [y]. W tym celu rozbijamy [f y], a oba
    wyrażenia okazują się być konwertowalne. *)

Lemma T4_illegal : False.
Proof.
  apply (Cantor' extract negb).
    destruct b; inversion 1.
    apply surjective_extract.
Qed.

(** Skoro mamy surjekcję z [T4] w [T4 -> bool], katastrofy nie da się
    uniknąć.

    Moglibyśmy się też zastanowić nad napisaniem zapętlającej się funkcji
    [loop], ale coś czuję, że ty coś czujesz, że byłoby to babranie się
    w niepotrzebnym problemie. Wobec tego (oczywiście o ile dotychczas
    się nie skapnąłeś) poczuj się oświecony! *)

Definition loop (x : T4) : bool := extract x x.

(** Ha! Tak tak, [loop] nie jest niczym innym niż lekko rozmnożoną wersją
    [extract]. *)

Lemma extract_c0 :
  forall f : ((T4 -> bool) -> nat) -> Color,
    extract (c0 f) =
      fun y =>
        match f (fun g => if g y then 0 else 1) with
        | R => true
        | _ => false
        end.
Proof.
  reflexivity.
Qed.

Lemma loop_nontermination :
  true = loop (c0 (
    fun g : (T4 -> bool) -> nat =>
    match g loop with
   | 0 => R
   | _ => G
    end)).
Proof.
  intros.
  unfold loop.
  rewrite 5!extract_c0.
Abort.

(** A skoro [loop] to tylko inne [extract], to nie powinno cię też wcale a
    wcale zdziwić, że najbardziej oczywisty argument, dla którego [loop]
    się zapętla, jest żywcem wzięty z dowodu [surjective_extract] (choć
    oczywiście musimy zastąpić [f] przez [loop]).

    Oczywiście niemożliwe jest, żeby formalnie udowodnić w Coqu, że coś
    się zapętla. Powyższy lemat ma być jedynie demonstracją - ręczne
    rozpisanie tego przykładu byłoby zbyt karkołomne. Jak widać z dowodu,
    przepisywanie równania definiującego [extract] tworzy wesołą piramidkę
    zrobioną z [match]ów i [if]ów. Jeżeli chcesz poczuć pełnię zapętlenia,
    wypbróuj taktykę [rewrite !eq] - zapętli się ona, gdyż równanie [eq]
    można przepisywać w nieskończoność. *)

End T4.

(** Mogłoby się wydawać, że teraz to już na pewno nasze metody działają na
    wszystkie możliwe negatywne typy induktywne. Cytując Tadeusza Sznuka:
    "Nic bardziej mylnego!". *)

Module T5.

Unset Positivity Checking.
Inductive T5 : Type :=
| c0 : (((T5 -> nat) -> bool) -> Color) -> T5.
Set Positivity Checking.

(** Rzućmy okiem na powyższy typ. Wygląda podobnie do poprzedniego, ale jest
    nieco inny - typy [nat] i [bool] zamieniły się miejscami. Jakie rodzi to
    konsekwencje? Sprawdźmy. *)

Definition extract : T5 -> T5 -> nat.
Proof.
  intros [f] y.
  apply (
    fun c : Color =>
    match c with
    | R => 0
    | G => 1
    | B => 2
    end).
  apply f. intro g.
  apply isZero. exact (g y).
Defined.

(** Definicja [extract] jest podobna jak poprzednio, ale tym razem konwertujemy
    [Color] na [nat] za pomocą funkcji, która nie jest surjekcją. *)

Lemma surjective_extract :
  surjective extract.
Proof.
  unfold surjective, extract.
  intro f.
  exists (c0 (
    fun g : (T5 -> nat) -> bool =>
    match g f with
    | true => R
    | false => B
    end)).
  extensionality y.
  destruct (f y); cbn.
    reflexivity.
Abort.

(** Dowód również przebiega podobnie jak poprzednio. Załamuje się on dopiero,
    gdy na samym końcu rozbijamy wyrażenie [f y] i upraszczamy używając [cbn].
    W pierwszym podcelu [0 = 0] jeszcze jakoś udaje się nam udowodnić, ale w
    drugim naszym oczom ukazuje się cel [2 = S n].

    Problem polega na tym, że [f y] może być dowolną liczbą naturalną, ale
    zastosowana przez nas funkcja konwertująca [Color -> nat] może zwracać
    jedynie [0], [1] lub [2]. Teraz widzimy jak na dłoni, skąd wziął się
    wymóg, by funkcja konwertująca była surjekcją. *)

Definition loop (x : T5) : nat := extract x x.

Lemma extract_eq :
  forall (f : ((T5 -> nat) -> bool) -> Color) (y : T5),
    extract (c0 f) y =
      match f (fun g : T5 -> nat => isZero (g y)) with
      | R => 0
      | G => 1
      | B => 2
      end.
Proof.
  reflexivity.
Qed.

Lemma loop_nontermination :
  42 = loop (c0 (
    fun g : (T5 -> nat) -> bool =>
    match g loop with
    | true => R
    | false => G
    end)).
Proof.
  unfold loop.
  rewrite extract_eq.
  rewrite 2!extract_eq.
Abort.

(** Co ciekawe, mimo że nie jesteśmy w stanie pokazać surjektywności [extract],
    to wciąż możemy użyć tej funkcji do zdefiniowania zapętlającej się
    funkcji [loop], zupełnie jak w poprzednim przykładzie.

    Niesmak jednak pozostaje, gdyż szczytem naszych ambicji nie powinno być
    ograniczanie się do zdefiniowania [loop], lecz do formalnego udowodnienia
    nielegalności [T5]. Czy wszystko stracone? Czy umrzemy? Tu dramatyczna
    pauza.

    Nie (w sensie że nie stracone, chociaż oczywiście umrzemy jak każdy).

    Okazuje się, że jest pewien trikowy sposób na rozwiązanie tego problemu,
    a mianowicie: zamiast próbować wyjąć z [T5] funkcję [T5 -> nat], wyjmiemy
    stamtąd po prostu funckję [T5 -> bool] i to mimo tego, że jej tam nie ma! *)

Definition extract' : T5 -> (T5 -> bool).
Proof.
  intros [f] y.
  apply (
    fun c : Color =>
    match c with
    | R => true
    | _ => false
    end).
  apply f. intro g.
  apply isZero. exact (g y).
Defined.

(** W kluczowych momentach najpierw konwertujemy [Color] na [bool] tak jak
    w jednym z poprzednich przykładów, a potem konwertujemy [nat] na [bool]
    za pomocą funkcji [isZero]. *)

Lemma surjective_extract' :
  surjective extract'.
Proof.
  unfold surjective, extract'.
  intro f.
  exists (c0 (
    fun g : (T5 -> nat) -> bool =>
      if g (fun t : T5 => if f t then 0 else 1) then R else G)).
  extensionality y.
  destruct (f y); cbn; reflexivity.
Qed.

(** Ponieważ obydwie nasze funkcję konwertujące były surjekcjami, możemy je
    teraz odwrócić i wykazać ponad wszelką wątpliwość, że [extract'] faktycznie
    jest surjekcją. *)

Lemma T5_illegal : False.
Proof.
  apply (Cantor' extract' negb).
    destruct b; inversion 1.
    apply surjective_extract'.
Qed.

(** Spróbujmy podsumować, co tak naprawdę stało się w tym przykładzie.

    Tym razem, mimo że do [T5] możemy włożyć dowolną funkcję [T5 -> nat],
    to nie możemy jej potem wyjąć, uzyskując surjekcję, gdyż zawadzają
    nam w tym typy po prawych stronach strzałek ([bool] i [Color]), które
    mają za mało elementów, żeby móc surjektywnie przekonwertować je na
    typ [nat].

    Jednak jeżeli mamy wszystkie możliwe funkcje typu [T5 -> nat], to
    możemy przerobić je (w locie, podczas "wyciągania") na wszystkie
    możliwe funkcje typu [T5 -> bool], składając je z odpowiednią
    surjekcją (np. [isZero]). Ponieważ typ [bool] i [Color] jesteśmy
    w stanie surjektywnie przekonwertować na [bool], reszta procesu
    działa podobnie jak w poprzednich przykładach. *)

Definition loop' (x : T5) : bool := extract' x x.

Lemma extract'_eq :
  forall (f : ((T5 -> nat) -> bool) -> Color) (y : T5),
    extract' (c0 f) y =
      match f (fun g : T5 -> nat => isZero (g y)) with
      | R => true
      | _ => false
      end.
Proof.
  reflexivity.
Qed.

Lemma loop_nontermination :
  true = loop' (c0 (
    fun g : (T5 -> nat) -> bool =>
    match g (fun t : T5 => if loop' t then 0 else 1) with
    | true => R
    | false => G
    end)).
Proof.
  unfold loop'.
  rewrite 3!extract'_eq.
Abort.

(** Takie trikowe [extract'] wciąż pozwala nam bez większych przeszkód
    zdefiniować zapętlającą się funkcję [loop']. Osiągnęliśmy więc
    pełen sukces.

    W ogólności nasz trik możnaby sformułować tak: jeżeli mamy konstruktor
    negatywny typu [T], to możemy wyjąć z niego funkcję [T -> A], gdzie [A]
    jest najmniejszym z typów występujących po prawych stronach strzałek. *)

End T5.

(** No, teraz to już na pewno mamy obcykane wszystkie przypadki, prawda?
    Tadeuszu Sznuku przybywaj: "Otóż nie tym razem!". *)

Module T6.

Unset Positivity Checking.
Inductive T6 : Type :=
| c0 : (((T6 -> unit) -> bool) -> Color) -> T6.
Set Positivity Checking.

(** Kolejnym upierdliwym przypadkiem, burzącym nawet nasz ostateczny
    trik, jest sytuacja, w której po prawej stronie strzałki wystąpi
    typ [unit]. Oczywiście zgodnie z trikiem możemy z [T6] wyciągnąć
    surjekcję [T6 -> unit], ale jest ona oczywiście bezużyteczna, bo
    taką samą możemy zrobić za darmo, stale zwracając po prostu [tt].
    Surjekcja z [T6] w [T6 -> unit] nie wystarczy rzecz jasna, żeby
    odpalić twierdzenie Cantora.

    Tym razem jednak nie powinniśmy spodziewać się, że upierdliwość tę
    będzie dało się jakoś obejść. Typ [T6 -> unit] jest jednoelementowy
    (jedynym elementem jest [fun _ => tt]) podobnie jak [unit]. Bardziej
    poetycko możemy powiedzieć, że [T6 -> unit] i [unit] są izomorficzne,
    czyli możemy bez żadnych strat konwertować elementy jednego z tych
    typów na elementy drugiego i z powrotem.

    Skoro tak, to typ konstruktora [c0], czyli
    [(((T6 -> unit) -> bool) -> Color) -> T6)], możemy równie dobrze
    zapisać jako [((unit -> bool) -> Color) -> T6)]. Zauważmy teraz,
    że [unit -> bool] jest izomorficzne z [bool], gdyż ma tylko dwa
    elementy, a mianowicie [fun _ => true] oraz [fun _ => false].
    Tak więc typ [c0] możemy jeszcze prościej zapisać jako
    [(bool -> Color) -> T6], a to oznacza, że typ [T6] jest jedynie
    owijką na funkcje typu [bool -> Color]. Twierdzenie Cantora nie
    pozwala tutaj uzyskać sprzeczności.

    Czy zatem typy takie jak [T6] sa legalne? Syntaktycznie nie - Coq
    odrzuca je podobnie jak wszystkie inne negatywne typy induktywne.
    Semantycznie również nie - o ile nie możemy tutaj uzyskać jawnej
    sprzeczności, to nasze rozważania o nieterminacji wciąż są w mocy.

    Przypomnij sobie poprzedni przykład i nieudaną próbę wyłuskania z
    [T5] surjekcji [T5 -> nat]. Udało nam się zaimplementować funkcję
    [extract], której surjektywności nie potrafiliśmy pokazać, ale pomimo
    tego bez problemu udało nam się użyć jej do napisania funkcji [loop].
    W obecnym przykładzie jest podobnie i nieterminacja to najlepsze, na
    co możemy liczyć. *)

(** **** Ćwiczenie *)

(** Zdefiniuj funkcję [extract], a następnie użyj jej do zdefiniowania
    funkcji [loop]. Zademonstruj w sposób podobny jak poprzednio, że
    [loop] się zapętla. Wskazówka: wszystko działa tak samo jak w
    poprzednim przykładzie. *)

(* begin hide *)
Definition extract (x y : T6) : unit :=
match x with
| c0 f =>
  match f (fun g => match g y with | tt => true end) with
  | R => tt
  | G => tt
  | B => tt
  end
end.

Definition loop (x : T6) : unit := extract x x.

Lemma extract_eq :
  forall f y,
    extract (c0 f) y =
      match f (fun g => match g y with | tt => true end) with
      | R => tt
      | G => tt
      | B => tt
      end.
Proof.
  reflexivity.
Qed.

Lemma loop_nontermination :
  tt = loop (c0 (
    fun g : (T6 -> unit) -> bool =>
    match g loop with
    | true => R
    | false => G
    end)).
Proof.
  unfold loop.
  rewrite extract_eq.
  rewrite 2!extract_eq.
Abort.
(* end hide *)

End T6.

(** No, teraz to już na pewno wiemy wszystko... *)

(** **** Ćwiczenie *)

(** Otóż nie do końca. Ostatnim hamulcowym, groźniejszym nawet niż [unit],
    jest wystąpienie po prawej stronie strzałki typu (czy raczej zdania)
    [False]. W tym przypadku nie tylko nie pomaga nam Cantor, ale nie
    pomaga też nieterminacja, gdyż najzwyczajniej w świecie nie da się
    zdefiniować żadnej funkcji.

    Jako, że za cholerę nie wiem, co z tym fantem zrobić, zostawiam go tobie
    jako ćwiczenie: wymyśl metodę pokazywania nielegalności negatywnych typów
    induktywnych, w których po prawej stronie strzałki jest co najmniej
    jedno wystąpienie [False]. *)

Module T7.

Unset Positivity Checking.
Inductive T7 : Type :=
| c0 : (((T7 -> bool) -> False) -> Color) -> T7.
Set Positivity Checking.

(* begin hide *)

(* TODO: [False] po prawej stronie strzałki w
   TODO: negatywnych typach induktywnych *)

Lemma wut :
  forall
    (f g : ((T7 -> bool) -> False) -> Color)
    (x   :  (T7 -> bool) -> False),
      f x = g x.
Proof.
  intros.
  destruct (x (fun _ => true)).
Qed.

Definition extract (x : T7) : T7 -> bool.
Proof.
  destruct x as [f].
  intro y.
  apply (
    fun c : Color =>
    match c with
    | R => true
    | _ => false
    end).
  apply f.
  intro g.
Abort.

(* end hide *)

End T7.

(** * Pozytywne typy induktywne *)

(** Na koniec rozprawimy się z pozytywnymi typami "induktywnymi" (ale tylko
    do pewnego stopnia; tak po prawdzie, to raczej one rozprawią się z
    nami). *)

Fail Inductive Pos : Type :=
| Pos0 : ((Pos -> bool) -> bool) -> Pos.
(* ===> The command has indeed failed with message:
        Non strictly positive occurrence of "Pos" in
        "((Pos -> bool) -> bool) -> Pos". *)

(** Coq odrzuca powyższą definicję typu [Pos], gdyż pierwsze wystąpienie [Pos]
    w typie konstruktora [Pos0] nie jest ściśle pozytywne. I faktycznie - gdy
    policzymy niedobrość tego wystąpienia zgodnie z naszym wzorem, to wyjdzie,
    że wynosi ona 2, gdyż [Pos] występuje na lewo od dwóch strzałek (pamiętaj,
    że najbardziej zewnętrzna strzałka, czyli ta, na prawo od której też jest
    [Pos], nie liczy się - wzór dotyczy tylko argumentów konstruktora, a nie
    całego konstruktora). *)

Unset Positivity Checking.
Inductive Pos : Type :=
| Pos0 : ((Pos -> bool) -> bool) -> Pos.
Set Positivity Checking.

(** Spróbujmy zawalczyć z typem [Pos] naszą metodą opartą o twierdzenie
    Cantora. *)

Definition extract (p : Pos) : Pos -> bool.
Proof.
  destruct p as [f]. intro y.
  apply f. intro z.
  apply f. intro w.
  (* ad infinitum *)
Abort.

(** Mogłoby się wydawać, że wyciągnięcie z [Pos] funkcji [Pos -> bool]
    nie może być trudniejsze, niż zabranie dziecku cukierka. Niestety
    jednak nie jest tak, gdyż w [Pos] tak naprawdę nie ma żadnej takiej
    funkcji - jest funkcja [(Pos -> bool) -> bool], a to już zupełnie
    coś innego.

    Żeby lepiej zrozumieć tę materię, musimy metaforycznie zinterpretować
    znany nam już współczynnik niedobrości i wynikający z niego podział
    na wystąpienia ściśle pozytywne, pozytywne i negatywne. Dzięki tej
    interpretacji dowiemy się też, dlaczego nieparzysta niedobrość jest
    negatywna, a niezerowa parzysta jest pozytywna.

    Najprościej jest zinterpretować wystąpienia ściśle pozytywne, gdyż
    mieliśmy już z nimi sporo do czynienia. Weźmy konstruktor
    [cons : A -> list A -> list A]. Jest tutaj jedno ściśle pozytywne
    wystąpienie typu [list A], które możemy interpretować tak: gdy
    używamy dopasowania do wzorca i dopasuje się [cons h t], to "mamy"
    element [t] typu [list A]. Ot i cała filozofia.

    Załóżmy teraz na chwilę, że Coq akceptuje negatywne i pozytywne
    typy induktywne. Co by było, gdybyśmy dopasowali konstruktor postaci
    [c : (T -> bool) -> T]? Tym razem nie mamy elementu typu [T], lecz
    funkcję [f : T -> bool]. Parafrazując: musimy "dać" funkcji [f]
    element typu [T], żeby dostać [bool].

    A co by było, gdybyśmy dopasowali konstruktor postaci
    [c : ((T -> bool) -> bool) -> T]? Tym razem również nie mamy żadnego
    elementu typu [T], lecz funkcję [f : ((T -> bool) -> bool)].
    Parafrazując: musimy dać funkcji [f] jakąś funkcję typu [T -> bool],
    żeby dostać [bool]. Ale gdy konstruujemy funkcję [T -> bool], to na
    wejściu dostajemy [T]. Tak więc początkowo nie mamy żadnego [T], ale
    gdy o nie poprosimy, to możemy je dostać. Ba! Jak pokazuje przykład,
    możemy dostać bardzo dużo [T].

    Taka właśnie jest różnica między ścisłą pozytywnością (mamy coś),
    negatywnością (musimy coś dać) i pozytywnością (możemy coś dostać,
    i to nawet w dużej liczbie sztuk). Zauważmy, że jedynie w przypadku
    negatywnym możemy wyjąć z [T] funkcję [T -> coś] (chyba, że zawadza
    nam [unit] lub [False]), bo to jedyny przypadek, gdy żądają od nas
    [T] (a skoro żądają [T], to muszą mieć funkcję, która coś z tym [T]
    zrobi). W przypadku pozytywnym nie ma żadnej takiej funkcji - to my
    dostajemy [T] i musimy coś z niego wyprodukować, więc to my jesteśmy
    tą funkcją!

    Ufff... mam nadzieję, że powyższa bajeczka jest sformułowana zrozumiale,
    bo lepszego wytłumaczenia nie udało mi się wymyślić.

    Moglibyśmy w tym miejscu zastanowić się, czy nie uda nam się pokazać
    sprzeczności choć na metapoziomie, poprzez napisanie nieterminującej
    funkcji [loop]. Szczerze pisząc, to niezbyt w to wierzę. Przypomnij
    sobie, że okazało się, że funkcja [loop] jest bardzo ściśle powiązana
    z funkcją [extract], zaś esencja nieterminacji polegała na przekazaniu
    do [loop] jako argument czegoś, co zawierało [loop] jako podterm
    (jeżeli nie zauważyłeś, to wszystkie nasze nieterminujące funkcje
    udało nam się zdefiniować bez użycia rekursji!). To daje nam jako taką
    podstawę by wierzyć, że nawet nieterminacja nie jest w tym przypadku
    osiągalna. *)

(* begin hide *)
Definition loop' : Pos -> bool.
Proof.
  intros [f].
  apply f. intro x.
Abort.

Fail Fixpoint loop' (x : Pos) : bool :=
match x with
| Pos0 f => f loop'
end.

(* end hide *)

(** W tym momencie należy sobie zadać zasadnicze pytanie: dlaczego w ogóle
    pozytywne typy induktywne są nielegalne? Przecież odróżnienie wystąpienia
    pozytywnego od negatywnego nie jest czymś trudnym, więc Coq nie może ich
    od tak po prostu nie rozróżniać - musi mieć jakiś powód!

    I faktycznie, powód jest. Nie ma on jednak wiele wspólnego z mechanizmem
    (pozytywnych) typów induktywnych samym w sobie, a z impredykatywnością
    sortu [Prop]. Trudne słowo, co? Nie pamiętam, czy już to wyjaśniałem,
    więc wyjaśnię jeszcze raz.

    Impredykatywność (lub też impredykatywizm) to pewna forma autoreferencji,
    która czasem jest nieszkodliwa, a czasem bardzo mordercza. Przyjrzyjmy
    się następującej definicji: "wujek Janusz to najbardziej wąsata osoba w
    tym pokoju". Definicja ta jest impredykatywna, gdyż definiuje ona wujka
    Janusza poprzez wyróżnienie go z pewnej kolekcji osób, ale definicja tej
    kolekcji osób musi odwoływać się do wujka Janusza ("w pokoju są wujek
    Janusz, ciocia Grażynka, Sebastianek i Karynka"). W Coqu impredykatywny
    jest sort [Prop], co ilustruje przykład: *)

Definition X : Prop := forall P : Prop, P.

(** Definicja zdania [X] jest impredykatywna, gdyż kwantyfikujemy w niej po
    wszystkich zdaniach ([forall P : Prop]), a zatem kwantyfikujemy także
    po zdaniu [X], które właśnie definiujemy.

    Impredykatywność sortu [Prop] jest niegroźna (no chyba, że pragniemy
    pozytywnych typów induktywnych, to wtedy jest), ale impredykatywność
    dla [Type] byłaby zabójcza, co zresztą powinien nam był uświadomić
    paradoks Russella.

    Dobra, koniec gadania. Poniższy przykład pośrednio pochodzi z sekcji
    3.1 pracy "Inductively defined types", której autorami są Thierry
    Coquand oraz Christine Paulin-Mohring, zaś bezpośrednio jest przeróbką
    kodu wziętego z
    vilhelms.github.io/posts/why-must-inductive-types-be-strictly-positive *)

Unset Positivity Checking.
Inductive Pos' : Type :=
| Pos'0 : ((Pos' -> Prop) -> Prop) -> Pos'.
Set Positivity Checking.

(** Jak widać, podejrzanym typem jest [Pos'], bliźniaczo podobne do [Pos],
    ale zamiast [bool] występuje tutaj [Prop].

    Tym razem jednak dowód sprzeczności będzie przebiegał nieco inaczej niż
    dotychczas. Poprzednio nasze plany sprowadzały się do tego, żeby wyjąć
    z nielegalnego typu induktywnego [T] jakąś funkcję [T -> A], co daje nam
    surjekcję [T -> (T -> A)], a to jest sprzeczne z twierdzeniem Cantora.

    Intuicja zaś stojąca za tym twierdzeniem (przynajmniej dla [A = bool])
    była taka, że funkcje [f : T -> bool] są zbiorami elementów typu [A] i
    jest ich przez to "więcej" niż elementów [T], czyli [T -> bool] jest
    większa niż [T]. Surjekcją z [T] w [T -> bool] oznacza jednak, że to
    [T] jest większe niż [T -> bool], co prowadzi do sprzeczności.

    Tym razem nie jesteśmy w stanie zrobić żadnej surjekcji, ale możemy za
    to zrobić injekcję. Intuicyjnie injekcja z [A] w [B] oznacza, że każdemu
    elementowi [A] można przypisać unikalny element [B]. Jeszcze intuicyjniej:
    typ [A] jest w jakimś sensie "mniejszy" niż typ [B], czyli jeszcze inaczej
    pisząc, typ [A] można "włożyć" lub "wstrzyknąć" (i stąd nazwa) do typu [B].

    Nasz plan polega więc na tym, żeby zdefiniować injekcję
    [(Pos' -> Prop) -> Pos'], co powinno jakoś prowadzić do sprzeczności:
    istnienie takiej injekcji oznacza, że [Pos' -> Prop] jest "mniejszy"
    niż [Pos'], ale z twierdzenia Cantora powinniśmy intuicyjnie czuć, że
    [Pos' -> Prop] jest większe niż [Pos']. *)

Definition f (P : Pos' -> Prop) : Pos' :=
  Pos'0 (fun Q : Pos' -> Prop => P = Q).

Lemma injective_f :
  forall P Q : Pos' -> Prop,
    f P = f Q -> P = Q.
Proof.
  unfold f.
  inversion 1.
  apply (f_equal (fun f => f Q)) in H1.
  rewrite H1.
  reflexivity.
Qed.

(** Definicja naszej injekcji jest dość prosta. Żeby przerobić [P : Pos' -> Prop]
    na [Pos'], używamy konstruktora [Pos'0], a jego argumentem jest po prostu
    funkcja, która porównuje swój argument do [P] używając relacji równości. *)

Definition wut (x : Pos') : Prop :=
  exists P : Pos' -> Prop, f P = x /\ ~ P x.

(** Tutaj następują czary, które używają impredykatywności.

    Definiujemy predykat [wut : Pos' -> Prop], który głosi, że funkcja [f] jest
    surjekcją (czyli [exists P, f P = x]), która ma dodatkowo tę właściwość, że
    predykat [P], któremu [f] przyporządkowuje [x], nie jest spełniony przez [x]
    (czyli [~ P x]).

    Parafrazując: [wut] to coś w stylu zbioru wszystkich [x : Pos'], które nie
    należą same same do siebie. Paradoks Russella jak malowany! Wielka zła
    autoreferencja czai się tuż za rogiem - ciekawe co by się stało, gdybyśmy
    rozważyli zdanie [wut (f wut)]... *)

Lemma paradox : wut (f wut) <-> ~ wut (f wut).
Proof.
  split.
    destruct 1 as (P & H1 & H2). intro H.
      apply injective_f in H1. subst. contradiction.
    intro H. red. exists wut. split.
      reflexivity.
      assumption.
Qed.

(** Ano, wszystko wybucha. Z lewa na prawo rozbijamy dowód [wut (f wut)] i
    dostajemy predykat [P]. Wiemy, że [f P = f wut], ale [f] jest injekcją,
    więc [P = wut]. To jednak kończy się sprzecznością, bo z jednej strony
    [wut (f wut)], ale z drugiej strony [~ P (f wut)], czyli [~ wut (f wut)].

    Z prawa na lewo jest łatwiej. Mamy [~ wut (f wut)] i musimy udowodnić
    [wut (f wut)]. Wystarczy, że istnieje pewien predykat [P], który spełnia
    [f P = f wut] i [~ P (f wut)]. Na [P] wybieramy oczywiście [wut]. Równość
    [f wut = f wut] zachodzi trywialnie, zaś [~ wut (f wut)] zachodzi na mocy
    założenia. *)

Lemma Pos'_illegal : False.
Proof.
  pose paradox. firstorder.
Qed.

(** No i bum. Jak widać, pozytywne typy induktywne prowadzą do sprzeczności,
    ale nie ma to z nimi wiele wspólnego, za to ma wiele wspólnego z sortem
    [Prop] i jego impredykatywnością. *)

(** * Podsumowanie (TODO) *)

(** W tym rozdziale poznaliśmy kryterium ścisłej pozytywności, które obowiązuje
    wszystkie definicje typów induktywnych. Dowiedzieliśmy się, że negatywne
    typy induktywne prowadzą do nieterminacji, która jest złem wcielonym.
    Poznaliśmy pojęcie surjekcji oraz twierdzenie Cantora, które również
    zabrania negatywnym typom induktywnym istnienia.

    Ostatecznie dowiedzieliśmy się, że pozytywne typy induktywne także są
    nielegalne, choć jesteśmy wobec nich raczej bezsilni, no chyba że
    chodzi o impredykatywny (tego słowa też się nauczyliśmy) sort [Prop]. *)