(** * X6: Rozdział z odpadami z R2 *)

(** * Parametryczność *)

(** UWAGA TODO: ten podrozdział zawiera do pewnego stopnia kłamstwa (tzn.
    dość uproszczony punkt widzenia). *)

(** Niech [A B : Set]. Zadajmy sobie następujące pytanie: ile jest funkcji
    typu [A -> B]? Żeby ułatwić sobie zadanie, ograniczmy się jedynie do
    typów, które mają skończoną ilość elementów.

    Nietrudno przekonać się, że ich ilość to |B|^|A|, gdzie ^ oznacza
    potęgowanie, zaś |T| to ilość elementów typu [T] (ta notacja nie ma
    nic wspólnego z Coqiem — zaadaptowałem ją z teorii zbiorów jedynie
    na potrzeby tego podrozdziału).

    Udowodnić ten fakt możesz (choć póki co nie w Coqu) posługując się
    indukcją po ilości elementów typu [A]. Jeżeli [A] jest pusty, to
    jest tylko jedna taka funkcja, o czym przekonałeś się już podczas
    ćwiczeń w podrozdziale o typie [Empty_set]. *)

(** **** Ćwiczenie *)

(** Udowodnij (nieformalnie, na papierze), że w powyższym akapicie nie
    okłamałem cię. *)

(** **** Ćwiczenie *)

(** Zdefiniuj wszystkie możliwe funkcje typu [unit -> unit], [unit -> bool]
    i [bool -> bool]. *)

(** Postawmy sobie teraz trudniejsze pytanie: ile jest funkcji typu
    [forall A : Set, A -> A]? W udzieleniu odpowiedzi pomoże nam
    parametryczność — jedna z właściwości Coqowego polimorfizmu.

    Stwierdzenie, że polimorfizm w Coqu jest parametryczny, oznacza, że
    funkcja biorąca typ jako jeden z argumentów działa w taki sam sposób
    niezależnie od tego, jaki typ przekażemy jej jako argument.

    Konsekwencją tego jest, że funkcje polimorficzne nie wiedzą (i nie
    mogą wiedzieć), na wartościach jakiego typu operują. Wobec tego
    elementem typu [forall A : Set, A -> A] nie może być funkcja, która
    np. dla typu [nat] stale zwraca [42], a dla innych typów po prostu
    zwraca przekazany jej argument.

    Stąd konkludujemy, że typ [forall A : Set, A -> A] ma tylko jeden
    element, a mianowicie polimorficzną funkcję identycznościową. *)

Definition id' : forall A : Set, A -> A :=
  fun (A : Set) (x : A) => x.

(** **** Ćwiczenie *)

(** Zdefiniuj wszystkie elementy następujących typów lub udowodnij, że
    istnienie choć jednego elementu prowadzi do sprzeczności:
    - [forall A : Set, A -> A -> A]
    - [forall A : Set, A -> A -> A -> A]
    - [forall A B : Set, A -> B]
    - [forall A B : Set, A -> B -> A]
    - [forall A B : Set, A -> B -> B]
    - [forall A B : Set, A -> B -> A * B]
    - [forall A B : Set, A -> B -> sum A B]
    - [forall A B C : Set, A -> B -> C]
    - [forall A : Set, option A -> A]
    - [forall A : Set, list A -> A] *)

(* begin hide *)
Theorem no_such_fun :
  (forall A B : Set, A -> B) -> False.
Proof.
  intros. exact (X nat False 42).
Qed.
(* end hide *)

(** TODO: tu opisać kłamstwo *)

Inductive path {A : Type} (x : A) : A -> Type :=
    | idpath : path x x.

Arguments idpath {A} _.

Axiom LEM : forall (A : Type), A + (A -> Empty_set).

Open Scope type_scope.

Definition bad' (A : Type) :
  {f : A -> A &
    (@path Type bool A * forall x : A, f x <> x) +
    ((@path Type bool A -> Empty_set) * forall x : A, f x = x)}.
Proof.
  destruct (LEM (@path Type bool A)).
    destruct p. esplit with negb. left. split.
      exact (@idpath Type bool).
      destruct x; cbn; inversion 1.
    esplit with (fun x : A => x). right. split.
      assumption.
      reflexivity.
Defined.

Definition bad (A : Type) : A -> A := projT1 (bad' A).

Lemma bad_is_bad :
  forall b : bool, bad bool b <> b.
Proof.
  intros. unfold bad. destruct bad'. cbn. destruct s as [[p H] | [p H]].
    apply H.
    destruct (p (idpath _)).
Defined.

Lemma bad_ist_gut :
  forall (A : Type) (x : A),
    (@path Type bool A -> Empty_set) -> bad A x = x.
Proof.
  unfold bad. intros A x p. destruct bad' as [f [[q H] | [q H]]]; cbn.
    destruct (p q).
    apply H.
Defined.

(** * Rozstrzygalność *)

Theorem excluded_middle :
  forall P : Prop, P \/ ~ P.
Proof.
  intro. left.
Restart.
  intro. right. intro.
Abort.

(** Próba udowodnienia tego twierdzenia pokazuje nam zasadniczą różnicę
    między logiką konstruktywną, która jest domyślną logiką Coqa, oraz
    logiką klasyczną, najpowszechniej znanym i używanym rodzajem logiki.

    Każde zdanie jest, w pewnym "filozoficznym" sensie, prawdziwe lub
    fałszywe i to właśnie powyższe zdanie oznacza w logice klasycznej.
    Logika konstruktywna jednak, jak już wiemy, nie jest logiką prawdy,
    lecz logiką udowadnialności i ma swoją interpretację obliczeniową.
    Powyższe zdanie w logice konstruktywnej oznacza: program komputerowy
    [exluded_middle] rozstrzyga, czy dowolne zdanie jest prawdziwe, czy
    fałszywe.

    Skonstruowanie programu o takim typie jest w ogólności niemożliwe,
    gdyż dysponujemy zbyt małą ilością informacji: nie wiemy czym jest
    zdanie [P], a nie posiadamy żadnego ogólnego sposobu dowodzenia lub
    obalania zdań o nieznanej nam postaci. Nie możemy np. użyć indukcji,
    gdyż nie wiemy, czy zdanie [P] zostało zdefiniowane induktywnie, czy
    też nie. W Coqu jedynym sposobem uzyskania termu o typie [forall
    P : Prop, P \/ ~ P] jest przyjęcie go jako aksjomat. *)

Theorem True_dec : True \/ ~ True.
Proof.
  left. trivial.
Qed.

(** Powyższe dywagacje nie przeszkadzają nam jednak w udowadnianiu,
    że reguła wyłączonego środka zachodzi dla pewnych konkretnych
    zdań. Zdanie takie będziemy nazywać zdaniami rozstrzygalnymi
    (ang. decidable). O pozostałych zdaniach będziemy mówić, że są 
    nierozstrzygalne (ang. undecidable). Ponieważ w Coqu wszystkie
    funkcje są rekurencyjne, a dowody to programy, to możemy powyższą
    definicję rozumieć tak: zdanie jest rozstrzygalne, jeżeli istnieje
    funkcja rekurencyjna o przeciwdzidzinie [bool], która sprawdza, czy
    jest ono prawdziwe, czy fałszywe.

    Przykładami zdań, predykatów czy problemów rozstrzygalnych są:
    - sprawdzanie, czy lista jest niepusta
    - sprawdzanie, czy liczba naturalna jest parzysta
    - sprawdzanie, czy dwie liczby naturalne są równe *)

(** Przykładem problemów nierozstrzygalnych są:
    - dla funkcji [f g : nat -> nat] sprawdzenie, czy
      [forall n : nat, f n = g n] — jest to w ogólności niemożliwe,
      gdyż wymaga wykonania nieskończonej ilości porównań (co nie
      znaczy, że nie da się rozwiązać tego problemu dla niektórych
      funkcji)
    - sprawdzenie, czy słowo o nieskończonej długości jest palindromem *)

(** **** Ćwiczenie *)

Theorem eq_nat_dec :
  forall n m : nat, n = m \/ ~ n = m.
(* begin hide *)
Proof.
  induction n as [| n']; destruct m as [| m'].
    left. trivial.
    right. inversion 1.
    right. inversion 1.
    destruct (IHn' m').
      left. subst. trivial.
      right. intro. inversion H0. subst. contradiction H. trivial.
Qed.
(* end hide *)

(** ** Techniczne apekty rozstrzygalności *)

(** Podsumowując powyższe rozważania, moglibyśmy stwierdzić: zdanie [P] jest
    rozstrzygalne, jeżeli istnieje term typu [P \/ ~ P]. Stwierdzenie takie
    nie zamyka jednak sprawy, gdyż bywa czasem mocno bezużyteczne.

    Żeby to zobrazować, spróbujmy użyć twierdzenia [eq_nat_dec] do napisania
    funkcji, która sprawdza, czy liczna naturalna [n] występuje na liście
    liczb naturalnych [l]: *)

Fail Fixpoint inb_nat (n : nat) (l : list nat) : bool :=
match l with
    | nil => false
    | cons h t =>
        match eq_nat_dec n h with
            | or_introl _ => true
            | _ => inb_nat n t
        end
end.

(** Coq nie akceptuje powyższego kodu, racząc nas informacją o błędzie: *)

(* Error:
   Incorrect elimination of "eq_nat_dec n h0" in the inductive type "or":
   the return type has sort "Set" while it should be "Prop".
   Elimination of an inductive object of sort Prop
   is not allowed on a predicate in sort Set
   because proofs can be eliminated only to build proofs. *)

(** Nasza porażka wynika z faktu, że do zdefiniowania funkcji, która
    jest programem (jej dziedzina i przeciwdziedzina są sortu [Set])
    próbowaliśmy użyć termu [eq_nat_dec n h], który jest dowodem
    (konkluzją [eq_nat_dec] jest równość, która jest sortu [Prop]).

    Mimo korespondencji Curry'ego-Howarda, która odpowiada za olbrzymie
    podobieństwo specyfikacji i zdań, programów i dowodów, sortu [Set]
    i sortu [Prop], są one rozróżniane i niesie to za sobą konsekwencje:
    podczas gdy programów możemy używać wszędzie, dowodów możemy używać
    jedynie do konstruowania innych dowodów.

    Praktycznie oznacza to, że mimo iż równość liczb naturalnych jest
    rozstrzygalna, pisząc program nie mamy możliwości jej rozstrzygania
    za pomocą [eq_nat_dec]. To właśnie miałem na myśli pisząc, że termy
    typu [P \/ ~ P] są mocno bezużyteczne.

    Uszy do góry: nie wszystko stracone! Jest to tylko drobna przeszkoda,
    którą bardzo łatwo ominąć: *)

Inductive sumbool (A B : Prop) : Set :=
    | left : A -> sumbool A B
    | right : B -> sumbool A B.

(** Typ [sumbool] jest niemal dokładną kopią [or], jednak nie żyje on
    w [Prop], lecz w [Set]. Ta drobna sztuczka, że termy typu
    [sumbool A B] formalnie są programami, mimo że ich naturalna
    interpretacja jest taka sama jak [or], a więc jako dowodu
    dysjunkcji. *)

(** **** Ćwiczenie *)

(** Udowodnij twierdzenie [eq_nat_dec'] o rozstrzygalności [=] na
    liczbach naturalnych. Użyj typu [sumbool]. Następnie napisz
    funkcję [inb_nat], która sprawdza, czy liczba naturalna [n]
    jest obecna na liście [l]. *)

(** * Pięć rodzajów reguł *)

(** Być może jeszcze tego nie zauważyłeś, ale większość logiki konstruktywnej,
    programowania funkcyjnego, a przede wszystkim teorii typów kręci się wokół
    pięciu rodzajów reguł.
    Są to reguły:
    - formacji (ang. formation rules)
    - wprowadzania (ang. introduction rules)
    - eliminacji (ang. elimination rules)
    - obliczania (ang. computation rules)
    - unikalności (ang. uniqueness principles) *)

(** W tym podrozdziale przyjrzymy się wszystkim pięciu typom reguł. Zobaczymy
    jak wyglądają, skąd się biorą i do czego służą. Podrozdział będzie miał
    charakter mocno teoretyczny. *)

(** ** Reguły formacji *)

(** Reguły formacji mówią nam, jak tworzyć typy (termy sortów [Set] i [Type])
    oraz zdania (termy sortu [Prop]). Większość z nich pochodzi z nagłówków
    definicji induktywnych. Reguła dla typu [bool] wygląda tak: *)

(*
    ----------
    bool : Set 
*)

(** Ten mistyczny zapis pochodzi z publikacji dotyczących teorii typów.
    Nad kreską znajdują się przesłanki reguły, a pod kreską znajduje się
    konkluzja reguły.

    Regułę tę możemy odczytać: [bool] jest typem sortu [Set]. Postać tej
    reguły wynika wprost z definicji typu [bool]. *)

Print bool.

(* ===> Inductive bool : Set :=  true : bool | false : bool *)

(** Powyższej regule formacji odpowiada tutaj fragment [Inductive bool : Set],
    który stwierdza po prostu, że [bool] jest typem sortu [Set].

    Nie zawsze jednak reguły formacji są aż tak proste. Reguła dla produktu
    wygląda tak: *)

(*
    A : Type, B : Type
    ------------------
    prod A B : Type
*)

(** Reguła formacji dla [prod] głosi: jeżeli [A] jest typem sortu [Type]
    oraz [B] jest typem sortu [Type], to [prod A B] jest typem sortu
    [Type]. Jest ona rzecz jasna konsekwencją definicji produktu. *)

Print prod.

(* ===> Inductive prod (A B : Type) : Type :=
          pair : A -> B -> A * B *)

(** Regule odpowiada fragment [Inductive prod (A B : Type) : Type]. To,
    co w regule jest nad kreską ([A : Type] i [B : Type]), tutaj występuje
    przed dwukropkiem, po prostu jako argumentu typu [prod]. Jak widać,
    nagłówek typu induktywnego jest po prostu skompresowaną formą reguły
    formacji.

    Należy zauważyć, że nie wszystkie reguły formacji pochodzą z definicji
    induktywnych. Tak wygląda reguła formacji dla funkcji (między typami
    sortu [Type]): *)

(*
    A : Type, B : Type
    ------------------
    A -> B : Type
*)

(** Reguła nie pochodzi z definicji induktywnej, gdyż typ funkcji [A -> B]
    jest typem wbudowanym i nie jest zdefiniowany indukcyjnie. *)

(** **** Ćwiczenie *)

(** Napisz, bez podglądania, jak wyglądają reguły formacji dla [option],
    [nat] oraz [list]. Następnie zweryfikuj swoje odpowiedzi za pomocą
    komendy [Print]. *)

(* begin hide *)

(*  [option]

    A : Type
    ---------------
    option A : Type
*)

(*  [nat]

    ---------
    nat : Set
*)

(*  [list]

    A : Type
    -------------
    list A : Type
*)

(* end hide *)

(** ** Reguły wprowadzania *)

(** Reguły wprowadzania mówią nam, w jaki sposób formować termy danego
    typu. Większość z nich pochodzi od konstruktorów typów induktywnych.
    Dla typu bool reguły wprowadzania wyglądają tak: *)

(*
    -----------
    true : bool

    ------------
    false : bool
*)

(** Reguły te stwierdzają po prostu, że [true] jest termem typu [bool]
    oraz że [false] jest termem typu [bool]. Wynikają one wprost z
    definicji typu [bool] — każda z nich odpowiada jednemu konstruktorowi.

    Wobec powyższego nie powinna zaskoczyć cię reguła wprowadzania dla
    produktu: *)

(*
    A : Type, B : Type, a : A, b : B
    --------------------------------
    pair A B a b : prod A B
*)

(** Jeżeli jednak zaskoczyła cię obecność w regule [A : Type] i [B : Type],
    przyjrzyj się dokładnie typowi konstruktora [pair]: *)

Check @pair.
(* ===> pair : forall A B : Type, A -> B -> A * B *)

(** Widać tutaj jak na dłoni, że [pair] jest funkcją zależną biorącą
    cztery argumenty i zwracają wynik, którego typ jest produktem jej
    dwóch pierwszych argumentów.

    Podobnie jak w przypadku reguł formacji, nie wszystkie reguły
    wprowadzania pochodzą od konstruktorów typów induktywnych. W
    przypadku funkcji reguła wygląda mniej więcej tak: *)

(*
    Γ |- A -> B : Type, Γ; x : T |- y : B
    -------------------------------------
    Γ |- fun x => y : A -> B
*)

(** Pojawiło się tu kilka nowych rzeczy: litera Γ oznacza kontekst,
    zaś zapis Γ |- j, że osąd j zachodzi w kontekście Γ. Zapis Γ; j
    oznacza rozszerzenie kontekstu Γ poprzez dodanie do niego osądu j.

    Regułę możemy odczytać tak: jeżeli [A -> B] jest typem sortu [Type]
    w kontekście Γ i [y] jest termem typu [B] w kontekście Γ rozszerzonym
    o osąd [x : T], to [fun x => y] jest termem typu [A -> B] w kontekście
    Γ.

    Powyższa reguła nazywana jest "lambda abstrakcją" (gdyż zazwyczaj jest
    zapisywana przy użyciu symbolu λ zamiast słowa kluczowego [fun], jak
    w Coqu). Nie przejmuj się, jeżeli jej. Znajomość reguł wprowadzania nie
    jest nam potrzebna, by skutecznie posługiwać się Coqiem.

    Należy też dodać, że reguła ta jest nieco uproszczona. Pełniejszy
    opis teoretyczny induktywnego rachunku konstrukcji można znaleźć
    w rozdziałach 4 i 5 manuala: https://coq.inria.fr/refman/toc.html *)

(** **** Ćwiczenie *)

(** Napisz (bez podglądania) jak wyglądają reguły wprowadzania dla
    [option], [nat] oraz [list]. Następnie zweryfikuj swoje odpowiedzi
    za pomocą komendy [Print]. *)

(* begin hide *)

(*  [option]

    A : Type
    -----------------
    None A : option A

    A : Type, x : A
    -----------------
    Some x : option A
*)

(*  [nat]

    -------
    0 : nat

    n : nat
    ---------
    S n : nat
*)

(*  [list]

    A : Type
    ------------
    nil A : Type

    A : Type, h : A, t : list A
    ---------------------------
    h :: t : list A
*)

(* end hide *)

(** ** Reguły eliminacji *)

(** Reguły eliminacji są w pewien sposób dualne do reguł wprowadzania.
    Tak jak reguły wprowadzania dla typu [T] służą do konstruowania
    termów typu [T] z innych termów, tak reguły eliminacji dla typu [T]
    mówią nam, jak z termów typu [T] skonstruować termy innych typów.

    Zobaczmy, jak wygląda jedna z reguł eliminacji dla typu [bool]. *)

(*
    A : Type, x : A, y : A, b : bool
    --------------------------------
    if b then x else y : A
*)

(** Reguła ta mówi nam, że jeżeli mamy typ [A] oraz dwie wartości
    [x] i [y] typu [A], a także term [b] typu [bool], to możemy
    skonstruować inną wartość typu [A], mianowicie [if b then x
    else y].

    Reguła ta jest dość prosta. W szczególności nie jest ona zależna,
    tzn. obie gałęzie [if]a muszą być tego samego typu. Przyjrzyjmy
    się nieco bardziej ogólnej regule. *)

(*
    P : bool -> Type, x : P true, y : P false, b : bool
    ----------------------------------------------------
    bool_rect P x y b : P b
*)

(** Reguła ta mówi nam, że jeżeli mamy rodzinę typów [P : bool -> Type]
    oraz termy [x] typu [P true] i [y] typu [P false], a także term [b]
    typu [bool], to możemy skonstruować term [bool_rect P x y b] typu
    [P b].

    Spójrzmy na tę regułę z nieco innej strony: *)

(*
    P : bool -> Type, x : P true, y : P false
    ----------------------------------------------------
    bool_rect P x y : forall b : bool, P b
*)

(** Widzimy, że reguły eliminacji dla typu induktywnego [T] służą do
    konstruowania funkcji, których dziedziną jest [T], a więc mówią
    nam, jak "wyeliminować" term typu [T], aby uzyskać term innego typu. 

    Reguły eliminacji występują w wielu wariantach:
    - zależnym i niezależnym — w zależności od tego, czy służą do definiowania
      funkcji zależnych, czy nie.
    - rekurencyjnym i nierekurencyjnym — te druge służą jedynie do
      przeprowadzania rozumowań przez przypadki oraz definiowania funkcji
      przez pattern matching, ale bez rekurencji. Niektóre typy nie mają
      rekurencyjnych reguł eliminacji.
    - pierwotne i wtórne — dla typu induktywnego [T] Coq generuje regułę
      [T_rect], którą będziemy zwać regułą pierwotną. Jej postać wynika
      wprost z definicji typu [T]. Reguły dla typów nieinduktywnych (np.
      funkcji) również będziemy uważać za pierwotne. Jednak nie wszystkie
      reguły są pierwotne — przekonamy się o tym w przyszłości, tworząc
      własne reguły indukcyjne.
*)

(** Zgodnie z zaprezentowaną klasyfikacją, pierwsza z naszych reguł jest:
    - niezależna, gdyż obie gałęzie [if]a są tego samego typu. Innymi słowy,
      definiujemy term typu [A], który nie jest zależny
    - nierekurencyjna, gdyż typ [bool] nie jest rekurencyjny i wobec tego
      może posiadać jedynie reguły nierekurencyjne
    - wtórna — regułą pierwotną dla [bool] jest [bool_rect] *)

(** Druga z naszych reguł jest:
    - zależna, gdyż definiujemy term typu zależnego [P b]
    - nierekurencyjna z tych samych powodów, co reguła pierwsza
    - pierwotna — Coq wygenerował ją dla nas automatycznie *)

(** W zależności od kombinacji powyższych cech reguły eliminacji mogą
    występować pod różnymi nazwami:
    - reguły indukcyjne są zależne i rekurencyjne. Służą do definiowania
      funkcji, których przeciwdziedzina jest sortu [Prop], a więc do
      dowodzenia zdań przez indukcję
    - rekursory to rekurencyjne reguły eliminacji, które służą do definiowania
      funkcji, których przeciwdziedzina jest sortu [Set] lub [Type] *)

(** Nie przejmuj się natłokiem nazw ani rozróżnień. Powyższą klasyfikację
    wymyśliłem na poczekaniu i nie ma ona w praktyce żadnego znaczenia.

    Zauważmy, że podobnie jak nie wszystkie reguły formacji i wprowadzania
    pochodzą od typów induktywnych, tak i nie wszystkie reguły eliminacji
    od nich pochodzą. Kontrprzykładem niech będzie reguła eliminacji dla
    funkcji (niezależnych): *)

(*
    A : Type, B : Type, f : A -> B, x : A
    -------------------------------------
    f x : B
*)

(** Reguła ta mówi nam, że jeżeli mamy funkcję [f] typu [A -> B] oraz
    argument [x] typu [A], to aplikacja funkcji [f] do argumentu [x]
    jest typu [B].

    Zauważmy też, że mimo iż reguły wprowadzania i eliminacji są w pewien
    sposób dualne, to istnieją między nimi różnice.

    Przede wszystkim, poza regułami wbudowanymi, obowiązuje prosta zasada:
    jeden konstruktor typu induktywnego — jedna reguła wprowadzania. Innymi
    słowy, reguły wprowadzania dla typów induktywnych pochodzą bezpośrednio
    od konstruktorów i nie możemy w żaden sposób dodać nowych. Są one w
    pewien sposób pierwotne i nie mamy nad nimi (bezpośredniej) kontroli.

    Jeżeli chodzi o reguły eliminacji, to są one, poza niewielką ilością
    reguł pierwotnych, w pewnym sensie wtórne —
    możemy budować je z pattern matchingu i rekursji strukturalnej i to
    właśnie te dwie ostatnie idee są w Coqu ideami pierwotnymi. Jeżeli
    chodzi o kontrolę, to możemy swobodnie dodawać nowe reguły eliminacji
    za pomocą twierdzeń lub definiując je bezpośrednio.

    Działanie takie jest, w przypadku nieco bardziej zaawansowanych
    twierdzeń niż dotychczas widzieliśmy, bardzo częste. Ba! Częste
    jest także tworzenie reguł eliminacji dla każdej funkcji z osobna,
    perfekcyjnie dopasowanych do kształtu jej rekursji. Jest to nawet
    bardzo wygodne, gdyż Coq potrafi automatycznie wygenerować dla nas
    takie reguły.

    Przykładem niestandardowej reguły może być reguła eliminacji dla
    list działająca "od tyłu": *)

(*
    A : Type, P : list A -> Prop,
    H : P [[]],
    H' : forall (h : A) (t : list A), P t -> P (t ++ [[h]])
    -------------------------------------------------------------
    forall l : list A, P l
*)

(** Póki co wydaje mi się, że udowodnienie słuszności tej reguły będzie dla
    nas za trudne. W przyszłości na pewno napiszę coś więcej na temat reguł
    eliminacji, gdyż ze względu na swój "otwarty" charakter są one z punktu
    widzenia praktyki najważniejsze.

    Tymczasem na otarcie łez zajmijmy się inną, niestandardową regułą dla
    list. *)

(** **** Ćwiczenie *)

(** Udowodnij, że reguła dla list "co dwa" jest słuszna. Zauważ, że komenda
    [Fixpoint] może służyć do podawania definicji rekurencyjnych nie tylko
    "ręcznie", ale także za pomocą taktyk.

    Wskazówka: użycie hipotezy indukcyjnej [list_ind_2] zbyt wcześnie
    ma podobne skutki co wywołanie rekurencyjne na argumencie, który
    nie jest strukturalnie mniejszy. *)

Module EliminationRules.

Require Import List.
Import ListNotations.

Fixpoint list_ind_2
  (A : Type) (P : list A -> Prop)
  (H0 : P []) (H1 : forall x : A, P [x])
  (H2 : forall (x y : A) (l : list A), P l -> P (x :: y :: l))
    (l : list A) : P l.
(* begin hide *)
Proof.
  destruct l as [| x [| y t]]; auto.
  apply H2. apply list_ind_2; auto.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Napisz funkcję [apply], odpowiadającą regule eliminacji dla funkcji
    (niezależnych). Udowodnij jej specyfikację.

    Uwaga: notacja "$$" na oznaczenie aplikacji funkcji pochodzi z języka
    Haskell i jest tam bardzo często stosowana, gdyż pozwala zaoszczędzić
    stawiania zbędnych nawiasów. *)

(* begin hide *)
Definition apply {A B : Type} (f : A -> B) (x : A) : B := f x.
(* end hide *)

Notation "f $ x" := (apply f x) (at level 5).

Theorem apply_spec :
  forall (A B : Type) (f : A -> B) (x : A), f $ x = f x.
(* begin hide *)
Proof. trivial. Qed.
(* end hide *)

End EliminationRules.

(** ** Reguły obliczania *)

(** Poznawszy reguły wprowadzania i eliminacji możemy zadać sobie pytanie:
    jakie są między nimi związki? Jedną z odpowiedzi na to pytanie dają
    reguły obliczania, które określają, w jaki sposób reguły eliminacji
    działają na obiekty stworzone za pomocą reguł wprowadzania. Zobaczmy
    o co chodzi na przykładzie. *)

(*
    A : Type, B : Type, x : A |- e : B, t : A
    -----------------------------------------
    (fun x : A => e) t ≡ e{x/t}
*)

(** Powyższa reguła nazywa się "redukcja beta". Mówi ona, jaki efekt ma
    aplikacja funkcji zrobionej za pomocą lambda abstrakcji do argumentu,
    przy czym aplikacja jest regułą eliminacji dla funkcji, a lambda
    abstrakcja — regułą wprowadzania.

    Możemy odczytać ją tak: jeżeli [A] i [B] są typami, zaś [e] termem
    typu [B], w którym występuje zmienna wolna [x] typu [A], to wyrażenie
    [(fun x : A => e) t] redukuje się (symbol ≡) do [e], w którym w miejsce
    zmiennej [x] podstawiono term [t].

    Zauważ, że zarówno symbol ≡ jak i notacja [e{x/t}] są tylko nieformalnymi
    zapisami i nie mają żadnego znaczenia w Coqu.

    Nie jest tak, że dla każdego typu jest tylko jedna reguła obliczania.
    Jako, że reguły obliczania pokazują związek między regułami eliminacji
    i wprowadzania, ich ilość można przybliżyć prostym wzorem:

    ## reguł obliczania = ## reguł eliminacji * ## reguł wprowadzania,

    gdzie ## to nieformalny symbol oznaczający "ilość". W Coqowej praktyce
    zazwyczaj oznacza to, że reguł obliczania jest nieskończenie wiele,
    gdyż możemy wymyślić sobie nieskończenie wiele reguł eliminacji.
    Przykładem typu, który ma więcej niż jedną regułę obliczania dla danej
    reguły eliminacji, jest [bool]: *)

(*
    P : bool -> Type, x : P true, y : P false
    -----------------------------------------
    bool_rect P x y true ≡ x

    P : bool -> Type, x : P true, y : P false
    -----------------------------------------
    bool_rect P x y false ≡ y
*)

(** Typ [bool] ma dwie reguły wprowadzania pochodzące od dwóch konstruktorów,
    a zatem ich związki z regułą eliminacji [bool_rect] będą opisywać dwie
    reguły obliczania. Pierwsza z nich mówi, że [bool_rect P x y true]
    redukuje się do [x], a druga, że [bool_rect P x y false] redukuje się do
    [y].

    Gdyby zastąpić w nich regułe [bool_rect] przez nieco prostszą regułę, w
    której nie występują typy zależne, to można by powyższe reguły zapisać
    tak: *)

(*
    A : Type, x : A, y : A
    -----------------------------------------
    if true then x else y ≡ x

    A : Type, x : A, y : A
    -----------------------------------------
    if false then x else y ≡ y
*)

(** Wygląda dużo bardziej znajomo, prawda?

    Na zakończenie wypadałoby napisać, skąd biorą się reguły obliczania. W
    nieco mniej formalnych pracach teoretycznych na temat teorii typów są
    one zazwyczaj uznawane za byty podstawowe, z których następnie wywodzi
    się reguły obliczania takich konstrukcji, jak np. [match].

    W Coqu jest na odwrót. Tak jak reguły eliminacji pochodzą od pattern
    matchingu i rekursji, tak reguły obliczania pochdzą od opisanych już
    wcześniej reguł redukcji (beta, delta, jota i zeta), a także konwersji
    alfa. *)

(** **** Ćwiczenie *)

(** Napisz reguły obliczania dla liczb naturalnych oraz list (dla reguł
    eliminacji [nat_ind] oraz [list_ind]). *)

(* begin hide *)

(*  Liczbt naturalne.

    P : nat -> Prop, H0 : P 0, HS : forall n : nat, P n -> P (S n)
    --------------------------------------------------------------
    nat_ind P H0 HS 0 ≡ H0

    P : nat -> Prop, H0 : P 0, HS : forall n : nat, P n -> P (S n), n : nat
    -----------------------------------------------------------------------
    nat_ind P H0 HS (S n) ≡ HS n (nat_ind P H0 HS n)

    Listy.

    A : Type, P : list A -> Prop, Hnil : P [],
    Hcons : forall (h : A) (t : list A), P t -> P (h :: t)
    ------------------------------------------------------
    list_ind A P Hnil Hcons [] ≡ Hnil

    A : Type, P : list A -> Prop, Hnil : P [],
    Hcons : forall (h : A) (t : list A), P t -> P (h :: t),
    h : A, t : list A
    -------------------------------------------------------
    list_ind A P Hnil Hcons (h :: t) ≡
    Hcons h t (list_ind A P Hnil Hcons t) *)

(* end hide *)

(** ** Reguły unikalności *)

(** Kolejną odpowiedzią na pytanie o związki między regułami wprowadzania
    i eliminacji są reguły unikalności. Są one dualne do reguł obliczania
    i określają, w jaki sposób reguły wprowadzania działają na obiekty
    pochodzące od reguł eliminacji. Przyjrzyjmy się przykładowi. *)

(*
    A : Type, B : Type, f : A -> B
    ------------------------------
    (fun x : A => f x) ≡ f
*)

(** Powyższa reguła unikalności dla funkcji jest nazywana "redukcją eta".
    Stwierdza ona, że funkcja stworzona za pomocą abstrakcji [fun x : A],
    której ciałem jest aplikacja [f x] jest definicyjnie równa funkcji [f].
    Regułą wprowadzania dla funkcji jest oczywiście abstrakcja, a regułą
    eliminacji — aplikacja.

    Reguły unikalności różnią się jednak dość mocno od reguł obliczania,
    gdyż zamiast równości definicyjnej ≡ mogą czasem używać standardowej,
    zdaniowej równości Coqa, czyli [=]. Nie do końca pasuje też do nich
    stwierdzenie, że określają działanie reguł wprowadzania na reguły
    eliminacji, gdyż zamiast reguł eliminacji mogą w nich występować
    inne byty, zdefiniowane jednak za pomocą reguł eliminacji. Zobaczmy
    o co chodzi na przykładzie. *)

(*
    A : Type, B : Type, p : A * B
    --------------------------------
    (fst p, snd p) = p
*)

(** Powyższa reguła głosi, że para, której pierwszym elementem jest pierwszy
    element pary [p], a drugim elementem — drugi element pary [p], jest w
    istocie równa parze [p]. W Coqu możemy ją wyrazić (i udowodnić) tak: *)

Theorem prod_uniq :
  forall (A B : Type) (p : A * B),
    (fst p, snd p) = p.
Proof.
  destruct p. cbn. trivial.
Qed.

(** Podsumowując, reguły unikalności występują w dwóch rodzajach:
    - dane nam z góry, niemożliwe do wyrażenia bezpośrednio w Coqu i
      używające równości definicyjnej, jak w przypadku redukcji eta
      dla funkcji
    - możliwe do wyrażenia i udowodnienia w Coqu, używające zwykłej
      równości, jak dla produktów i w ogólności dla typów induktywnych *)

(** **** Ćwiczenie *)

(** Sformułuj reguły unikalności dla funkcji zależnych ([forall]), sum
    zależnych ([sigT]) i [unit] (zapisz je w notacji z poziomą kreską).
    Zdecyduj, gdzie w powyższej klasyfikacji mieszczą się te reguły.
    Jeżeli to możliwe, wyraź je i udowodnij w Coqu. *)

(* begin hide *)

(*
    A : Type, P : A -> Type, f : forall x : A, P x
    ----------------------------------------------
    (fun x : A => f x) ≡ f
*)

(*
    A : Type, P : A -> Type, p : {x : A & P x}
    ------------------------------------------
    (projT1 p, projT2 p) = p
*)

(*
    u : unit
    --------
    u = tt
*)

(** Reguła dla funkcji jest pierwszego typu, zaś reguły dla sum zależnych i
    [unit] są drugiego typu. *)

Theorem sigT_uniq :
  forall (A : Type) (P : A -> Type) (p : {x : A & P x}),
    existT P (projT1 p) (projT2 p) = p.
Proof.
  intros. destruct p. cbn. f_equal.
Qed.

Theorem unit_uniq :
  forall u : unit, u = tt.
Proof.
  destruct u. trivial.
Qed.

(* end hide *)

(** * Typy hybrydowe *)

(** Ostatnim z typów istotnych z punktu widzenia silnych specyfikacji
    jest typ o wdzięcznej nazwie [sumor]. *)

Module sumor.

Inductive sumor (A : Type) (B : Prop) : Type :=
    | inleft : A -> sumor A B
    | inright : B -> sumor A B.

(** Jak sama nazwa wskazuje, [sumor] jest hybrydą sumy rozłącznej [sum]
    oraz dysjunkcji [or]. Możemy go interpretować jako typ, którego
    elementami są elementy [A] albo wymówki w stylu "nie mam elementu [A],
    ponieważ zachodzi zdanie [B]". [B] nie zależy od [A], a więc jest to
    zwykła suma (a nie suma zależna, czyli uogólnienie produktu). [sumor]
    żyje w [Type], a więc jest to specyfikacja i liczy się konkretna
    postać jego termów, a nie jedynie fakt ich istnienia. *)

(** **** Ćwiczenie ([pred']) *)

(** Zdefiniuj funkcję [pred'], która przypisuje liczbie naturalnej jej
    poprzednik. Poprzednikiem [0] nie powinno być [0]. Mogą przydać ci
    się typ [sumor] oraz sposób definiowania za pomocą taktyk, omówiony
    w podrozdziale dotyczącym sum zależnych. *)

(* begin hide *)
Definition pred' (n : nat) : sumor nat (n = 0) :=
match n with
    | 0 => inright _ _ eq_refl
    | S n' => inleft _ _ n'
end.
(* end hide *)

End sumor.

(** * Small scale reflection *)

(* begin hide *)

Inductive even : nat -> Prop :=
    | even0 : even 0
    | evenSS : forall n : nat, even n -> even (S (S n)).

(*
Function evenb (n : nat) : bool :=
match n with
    | 0 => true
    | 1 => false
    | S (S n') => evenb n'
end.

Lemma evenb_spec :
  forall n : nat, evenb n = true -> even n.
Proof.
  intros. functional induction evenb n.
    constructor.
    congruence.
    constructor. auto.
Qed.

Goal even 666.
Proof.
  apply evenb_spec. cbn. trivial.
Qed.

Print Unnamed_thm.
Print evenb_spec.
*)

(** Wrzucić tu przykład z porządkiem leksykograficznym z bloga Mondet.
    Dać też przykład z permutacjami? *)

(** * Matching terms *)

(** TODO:
    - match expr
    - lazymatch expr
    - multimatch expr
    - type of term
    - eval redexpr
    - constr/uconstr/ltac
    - type_term ? *)

(** * Tactics for dealing with unification *)

(** TODO:
    - [has_evar], [is_evar], [is_var]
    - [unify]
    - [constr_eq]
    - [instantiate]
    - [quote] *)

(** * Functional programming in Ltac *)

(** Wstawić tutaj przykłady podobne do tych, które opisuje Chlipala. Być
    może jakiś większy development, tzn. zaprogramować listy w dwóch
    wersjach (zwykłe i zrobione produktem i unitem). *)

(** * Big scale reflection *)

(** Przykłady:
    - logika boolowska, czyli legitne [btauto]
    - permutacje
    - formuły logiczne
    - upraszczanie w monoidzie *)

(* end hide *)