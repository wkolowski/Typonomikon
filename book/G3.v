(** * G3: Zaawansowane typy induktywne [TODO] *)

(** W tym rozdziale będzie o mechanizmach definiowania typów induktywnych,
    które nie są dostępne w Coqu i w związku z tym musimy uciekać się do
    różnych sztuczek, żeby je zasymulować. *)

(** * Typy ilorazowe i smart konstruktory (TODO) *)

(* TODO: Tutaj może liczby wymierne, regexy albo coś w ten deseń? *)

(** * Struktury cykliczne (TODO) *)

(** * Prawdziwie zagnieżdżone typy induktywne (TODO) *)

(* TODO: Tutaj rzeczy z code/Cyclic.v oraz code/Cyclic2.v *)

(** * Wyższe czary *)

(** Najwyższy czas nauczyć się czegoś tak zaawansowanego, że nawet w Coqu
    (pełnym przecież dziwnych rzeczy) tego nie ma i nie zapowiada się na
    to, że będzie. Mam tu na myśli mechanizmy takie jak indukcja-indukcja,
    indukcja-rekursja oraz indukcja-indukcja-rekursja (jak widać, w świecie
    poważnych uczonych, podobnie jak świecie Goebbelsa, im więcej razy
    powtórzy się dane słowo, tym więcej płynie z niego mocy). *)

(** ** Przypomnienie *)

(** Zanim jednak wyjaśnimy, co to za stwory, przypomnijmy sobie różne, coraz
    bardziej innowacyjne sposoby definiowania przez indukcję oraz dowiedzmy
    się, jak sformułować i udowodnić wynikające z nich reguły rekursji oraz
    indukcji. *)

Unset Elimination Schemes.

(** Powyższa komenda mówi Coqowi, żeby nie generował automatycznie reguł
    indukcji. Przyda nam się ona, by uniknąć konfliktów nazw z regułami,
    które będziemy pisać ręcznie. *)

(** *** Enumeracje *)

Module enum.

Inductive I : Type :=
| c0 : I
| c1 : I
| c2 : I.

(** Najprymitywniejszymi z typów induktywnych są enumeracje. Definiując je,
    wymieniamy po prostu wszystkie ich elementy. *)

Definition I_case_nondep_type : Type :=
  forall P : Type, P -> P -> P -> I -> P.

(** Reguła definiowania przez przypadki jest banalnie prosta: jeżeli w
    jakimś inny typie [P] uda nam się znaleźć po jednym elemencie dla każdego
    z elementów naszego typu [I], to możemy zrobić funkcję [I -> P]. *)

Definition I_case_nondep : I_case_nondep_type :=
  fun (P : Type) (c0' c1' c2' : P) (i : I) =>
  match i with
  | c0 => c0'
  | c1 => c1'
  | c2 => c2'
  end.

(** Regułę zdefiniować możemy za pomocą dopasowania do wzorca. *)

Definition I_case_dep_type : Type :=
  forall (P : I -> Type) (c0' : P c0) (c1' : P c1) (c2' : P c2),
    forall i : I, P i.

(** Zależną regułę definiowania przez przypadki możemy uzyskać z poprzedniej
    uzależniając przeciwdziedzinę [P] od dziedziny. *)

Definition I_case_dep : I_case_dep_type :=
  fun (P : I -> Type) (c0' : P c0) (c1' : P c1) (c2' : P c2) (i : I) =>
  match i with
  | c0 => c0'
  | c1 => c1'
  | c2 => c2'
  end.

(** Definicja, jak widać, jest taka sama jak poprzednio, więc obliczeniowo
    obie reguły zachowują się tak samo. Różnica leży jedynie w typach -
    druga reguła jest ogólniejsza. *)

End enum.

(** *** Konstruktory rekurencjne *)

Module rec.

Inductive I : Type :=
| x : I -> I
| D : I -> I.

(** Typy induktywne stają się naprawdę induktywne, gdy konstruktory mogą
    brać argumenty typu, który właśnie definiujemy. Dzięki temu możemy
    tworzyć type, które mają nieskończenie wiele elementów, z których
    każdy ma kształt takiego czy innego drzewa. *)

Definition I_rec_type : Type :=
  forall P : Type,  (P -> P) -> (P -> P) -> I -> P.

(** Typ reguły rekursji (czyli rekursora) tworzymy tak jak dla enumeracji:
    jeżeli w typie [P] znajdziemy rzeczy o takim samym kształcie jak
    konstruktory typu [I], to możemy zrobić funkcję [I -> P]. W naszym
    przypadku oba konstruktory mają kształt [I -> I], więc do zdefiniowania
    naszej funkcji musimy znaleźć odpowiadające im rzeczy typu [P -> P]. *)

Fixpoint I_rec (P : Type) (x' : P -> P) (D' : P -> P) (i : I) : P :=
match i with
| x i' => x' (I_rec P x' D' i')
| D i' => D' (I_rec P x' D' i')
end.

(** Definicja rekursora jest prosta. Jeżeli wyobrazimy sobie [i : I] jako
    drzewo, to węzły z etykietką [x] zastępujemy wywołaniem funkcji [x'],
    a węzły z etykietką [D] zastępujemy wywołaniami funkcji [D]. *)

Definition I_ind_type : Type :=
  forall (P : I -> Type)
    (x' : forall i : I, P i -> P (x i))
    (D' : forall i : I, P i -> P (D i)),
      forall i : I, P i.

(** Reguła indukcji (czyli induktor - cóż za piękna nazwa!) powstaje z
    reguły rekursji przez uzależnienie przeciwdziedziny [P] od dziedziny
    [I]. *)

Fixpoint I_ind (P : I -> Type)
  (x' : forall i : I, P i -> P (x i)) (D' : forall i : I, P i -> P (D i))
  (i : I) : P i :=
match i with
| x i' => x' i' (I_ind P x' D' i')
| D i' => D' i' (I_ind P x' D' i')
end.

(** Podobnie jak poprzednio, implementacja reguły indukcji jest identyczna
    jak rekursora, jedynie typy są bardziej ogólnej.

    Uwaga: nazywam reguły nieco inaczej niż te autogenerowane przez Coqa.
    Dla Coqa reguła indukcji dla [I] to nasze [I_ind] z [P : I -> Type]
    zastąpionym przez [P : I -> Prop], zaś Coqowe [I_rec] odpowiadałoby
    naszemu [I_ind] dla [P : I -> Set].

    Jeżeli smuci cię burdel nazewniczy, to nie przejmuj się - kiedyś będzie
    lepiej. Klasyfikacja reguł jest prosta:
    - reguły mogą być zależne lub nie, w zależności od tego czy [P] zależy
      od [I]
    - reguły mogą być rekurencyjne lub nie
    - reguły mogą być dla sortu [Type], [Prop] albo nawet [Set] *)

End rec.

(** *** Parametry *)

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

(** A regułę indukcję uzyskujemy przez uzależnienie [P] od [I]. *)

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

(** *** Indukcja wzajemna *)

Module mutual.

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

End mutual.

(** *** Indeksy *)

Module index.

Inductive I : nat -> Type :=
| c0 : bool -> I 0
| c42 : nat -> I 42.

(** Ostatnią poznaną przez nas innowacją są typy indeksowane. Tutaj również
    definiujemy za jednym zamachem (ekhem...) dużo typów, ale nie są one
    niezależne jak w przypadku parametrów, lecz mogą od siebie wzajemnie
    zależeć. Słowem, tak naprawdę definiujemy przez indukcję funkcję
    typu [A_1 -> ... -> A_n -> Type/Prop], gdzie [A_i] to indeksy. *)

Definition I_case_very_nondep_type : Type :=
  forall (P : Type) (c0' : bool -> P) (c42' : nat -> P),
    forall n : nat, I n -> P.

Definition I_case_very_nondep
  (P : Type) (c0' : bool -> P) (c42' : nat -> P)
  {n : nat} (i : I n) : P :=
match i with
| c0 b => c0' b
| c42 n => c42' n
end.

(** Możliwych reguł analizy przypadków mamy tutaj trochę więcej niż w
    przypadku parametrów. W powyższej regule [P] nie zależy od indeksu
    [n : nat]... *)

Definition I_case_nondep_type : Type :=
  forall (P : nat -> Type) (c0' : bool -> P 0) (c42' : nat -> P 42),
    forall n : nat, I n -> P n.

Definition I_case_nondep
  (P : nat -> Type) (c0' : bool -> P 0) (c42' : nat -> P 42)
  {n : nat} (i : I n) : P n :=
match i with
| c0 b => c0' b
| c42 n => c42' n
end.

(** ... a w powyższej tak. Jako, że indeksy zmieniają się pomiędzy
    konstruktorami, każdy z nich musi kwantyfikować je osobno (co akurat
    nie jest potrzebne w naszym przykładzie, gdyż jest zbyt prosty). *)

Definition I_case_dep_type : Type :=
  forall (P : forall n : nat, I n -> Type)
    (c0' : forall b : bool, P 0 (c0 b))
    (c42' : forall n : nat, P 42 (c42 n)),
      forall (n : nat) (i : I n), P n i.

Definition I_case_dep
  (P : forall n : nat, I n -> Type)
  (c0' : forall b : bool, P 0 (c0 b))
  (c42' : forall n : nat, P 42 (c42 n))
  (n : nat) (i : I n) : P n i :=
match i with
| c0 b => c0' b
| c42 n => c42' n
end.

(** Ogólnie reguła jest taka: reguła niezależna (pierwsza) nie zależy od
    niczego, a zależna (trzecia) zależy od wszystkiego. Reguła druga jest
    pośrednia - ot, take ciepłe kluchy. *)

End index.

(** Nie zapomnijmy ponownie nakazać Coqowi generowania reguł indukcji. *)
Set Elimination Schemes.

(** ** Indukcja-indukcja *)

Require Import List.
Import ListNotations.

Module ind_ind.

(** Po powtórce nadszedł czas nowości. Zacznijmy od nazwy, która jest iście
    kretyńska: indukcja-indukcja. Każdy rozsądny człowiek zgodzi się,
    że dużo lepszą nazwą byłoby coś w stylu "indukcja wzajemna indeksowana".

    Ta alternatywna nazwa rzuca sporo światła: indukcja-indukcja to połączenie
    i uogólnienie mechanizmów definiowania typów wzajemnie induktywnych oraz
    indeksowanych typów induktywnych.

    Typy wzajemnie induktywne mogą odnosić się do siebie nawzajem, ale co
    to dokładnie znaczy? Ano to, że konstruktory każdego typu mogą brać
    argumenty wszystkch innych typów definiowanych jednocześnie z nim. To
    jest clou całej sprawy: konstruktory.

    A co to ma do typów indeksowanych? Ano, zastanówmy się, co by się stało,
    gdybyśmy chcieli zdefiniować przez wzajemną indukcję typ [A] oraz rodzinę
    typów [B : A -> Type]. Otóż nie da się: konstruktory [A] mogą odnosić
    się do [B] i vice-versa, ale [A] nie może być indeksem [B].

    Indukcja-indukcja to coś, co... tam taram tam tam... pozwala właśnie na
    to: możemy jednocześnie zdefiniować typ i indeksowaną nim rodzinę typów.
    I wszystko to ukryte pod taką smutną nazwą... lobby teoriotypowe nie
    chciało, żebyś się o tym dowiedział.

    Czas na przykład! *)

Fail

Inductive slist {A : Type} (R : A -> A -> Prop) : Type :=
| snil : slist R
| scons : forall (h : A) (t : slist A), ok h t -> slist A

with ok {A : Type} {R : A -> A -> Prop} : A -> slist R -> Prop :=
| ok_snil : forall x : A, ok x snil
| ok_scons :
    forall (h : A) (t : slist A) (p : ok h t) (x : A),
      R x h -> ok x (scons h t p).

(* ===> The reference slist was not found in the current environment. *)

(** Jako się już wcześniej rzekło, indukcja-indukcja nie jest wspierana
    przez Coqa - powyższa definicja kończy się informacją o błędzie: Coq
    nie widzi [slist] kiedy czyta indeksy [ok] właśnie dlatego, że nie
    dopuszcza on możliwości jednoczesnego definiowania rodziny (w tym
    wypadku relacji) [ok] wraz z jednym z jej indeksów, [slist].

    Będziemy zatem musieli poradzić sobie z przykładem jakoś inaczej -
    po prostu damy go sobie za pomocą aksjomatów. Zanim jednak to zrobimy,
    omówimy go dokładniej, gdyż deklarowanie aksjomatów jest niebezpieczne
    i nie chcemy się pomylić.

    Zamysłem powyższego przykładu było zdefiniowanie typu list posortowanych
    [slist R], gdzie [R] pełni rolę relacji porządku, jednocześnie z relacją
    [ok : A -> slist R -> Prop], gdzie [ok x l] wyraża, że dostawienie [x]
    na początek listy posortowanej [l] daje listę posortowaną.

    Przykład jest oczywiście dość bezsensowny, bo dokładnie to samo można
    osiągnąć bez używania indukcji-indukcji - wystarczy najpierw zdefiniować
    listy, a potem relację bycia listą posortowaną, a na koniec zapakować
    wszystko razem. Nie będziemy się tym jednak przejmować.

    Definicja [slist R] jest następująca:
    - [snil] to lista pusta
    - [scons] robi posortowaną listę z głowy [h] i ogona [t] pod warunkiem, że
      dostanie też dowód zdania [ok h t] mówiącego, że można dostawić [h] na
      początek listy [t] *)

(** Definicja [ok] też jest banalna:
    - każdy [x : A] może być dostawiony do pustej listy
    - jeżeli mamy listę [scons h t p] oraz element [x], o którym wiemy,
      że jest mniejszy od [h], tzn. [R x h], to [x] może zostać dostawiony
      do listy [scons h t p] *)

(** Jak powinny wyglądać reguły rekursji oraz indukcji? Na szczęście wciąż
    działają schematy, które wypracowaliśmy dotychczas.

    Reguła rekursji mówi, że jeżeli znajdziemy w typie [P] coś o kształcie
    [slist R], a w relacji [Q] coś o kształcie [ok], to możemy zdefiniować
    funkcję [slist R -> P] oraz [forall (x : A) (l : slist R), ok x l -> Q].

    Regułe indukcji można uzyskać dodając tyle zależności, ile tylko zdołamy
    unieść.

    Zobaczmy więc, jak zrealizować to wszystko za pomocą aksjomatów. *)

Axioms
  (slist : forall {A : Type}, (A -> A -> Prop) -> Type)
  (ok : forall {A : Type} {R : A -> A -> Prop}, A -> slist R -> Prop).

(** Najpierw musimy zadeklarować [slist], gdyż wymaga tego typ [ok]. Obie
    definicje wyglądają dokładnie tak, jak nagłówki w powyższej definicji
    odrzuconej przez Coqa.

    Widać też, że gdybyśmy chcieli zdefiniować rodziny [A] i [B], które są
    nawzajem swoimi indeksami, to nie moglibyśmy tego zrobić nawet za pomocą
    aksjomatów. Rodzi to pytanie o to, które dokładnie definicje przez
    indukcję-indukcję są legalne. Odpowiedź brzmi: nie wiem, ale może kiedyś
    się dowiem. *)

Axioms
  (snil : forall {A : Type} {R : A -> A -> Prop}, slist R)
  (scons :
    forall {A : Type} {R : A -> A -> Prop} (h : A) (t : slist R),
      ok h t -> slist R)
  (ok_snil :
    forall {A : Type} {R : A -> A -> Prop} (x : A), ok x (@snil _ R))
  (ok_scons :
    forall
      {A : Type} {R : A -> A -> Prop}
      (h : A) (t : slist R) (p : ok h t)
      (x : A), R x h -> ok x (scons h t p)).

(** Następnie definiujemy konstruktory: najpierw konstruktory [slist], a
    potem [ok]. Musimy to zrobić w tej kolejności, bo konstruktor [ok_snil]
    odnosi się do [snil], a [ok_scons] do [scons].

    Znowu widzimy, że gdyby konstruktory obu typów odnosiły się do siebie
    nawzajem, to nie moglibyśmy zdefiniować takiego typu aksjomatycznie. *)

Axiom
  (ind : forall
    (A : Type) (R : A -> A -> Prop)
    (P : slist R -> Type)
    (Q : forall (h : A) (t : slist R), ok h t -> Type)
    (Psnil : P snil)
    (Pscons :
      forall (h : A) (t : slist R) (p : ok h t),
        P t -> Q h t p -> P (scons h t p))
    (Qok_snil : forall x : A, Q x snil (ok_snil x))
    (Qok_scons :
      forall
        (h : A) (t : slist R) (p : ok h t)
        (x : A) (H : R x h),
          P t -> Q h t p -> Q x (scons h t p) (ok_scons h t p x H)),
    {f : (forall l : slist R, P l) &
    {g : (forall (h : A) (t : slist R) (p : ok h t), Q h t p) |
      f snil = Psnil /\
      (forall (h : A) (t : slist R) (p : ok h t),
        f (scons h t p) = Pscons h t p (f t) (g h t p)) /\
      (forall x : A,
        g x snil (ok_snil x) = Qok_snil x) /\
      (forall
        (h : A) (t : slist R) (p : ok h t)
        (x : A) (H : R x h),
          g x (scons h t p) (ok_scons h t p x H) =
          Qok_scons h t p x H (f t) (g h t p))
    }}).

(** Ugh, co za potfur. Spróbujmy rozłożyć go na czynniki pierwsze.

    Przede wszystkim, żeby za dużo nie pisać, zobaczymy tylko regułę indukcji.
    Teoretycznie powinny to być dwie reguły (tak jak w przypadku [Smok]a i
    [Zmok]a) - jedna dla [slist] i jedna dla [ok], ale żeby za dużo nie
    pisać, możemy zapisać je razem.

    Typ [A] i relacja [R] są parametrami obu definicji, więc skwantyfikowane
    są na samym początku. Nasza reguła pozwala nam zdefiniować przez wzajemną
    rekursję dwie funkcje, [f : forall l : slist R, P l] oraz
    [g : forall (h : A) (t : slist R) (p : ok h t), Q h t p]. Tak więc [P]
    to kodziedzina [f], a [Q] - [g].

    Teraz potrzebujemy rozważyć wszystkie możliwe przypadki - tak jak przy
    dopasowaniu do wzorca. Przypadek [snil] jest dość banalny. Przypadek
    [scons] jest trochę cięższy. Przede wszystkim chcemy, żeby konkluzja
    była postaci [P (scons h t p)], ale jak powinny wyglądać hipotezy
    indukcyjne?

    Jedyna słuszna odpowiedź brzmi: odpowiadają one typom wszystkich możliwych
    wywołań rekurencyjnych [f] i [g] na strukturalnych podtermach
    [scons h t p]. Jedynymi typami spełniającymi te warunki są [P t] oraz
    [Q h t p], więc dajemy je sobie jako hipotezy indukcyjne.

    Przypadki dla [Q] wyglądają podobnie: [ok_snil] jest banalne, a dla
    [ok_scons] konkluzja musi być jedynej słusznej postaci, a hipotezami
    indukcyjnymi jest wszystko, co pasuje.

    W efekcie otrzymujemy dwie funkcje, [f] i [g]. Tym razem następuje jednak
    mały twist: ponieważ nasza definicja jest aksjomatyczna, zagwarantować
    musimy sobie także reguły obliczania, które dotychczas były zamilaczne,
    bo wynikały z definicji przez dopasowanie do wzorca. Teraz wszystkie te
    "dopasowania" musimy napisać ręcznie w postaci odpowiednio
    skwantyfikowanych równań. Widzimy więc, że [Psnil], [Pscons], [Qok_snil]
    i [Qok_scons] odpowiadają klauzulom w dopasowaniu do wzorca.

    Ufff... udało się. Tak spreparowaną definicją aksjomatyczną możemy się
    jako-tako posługiwać: *)

Definition rec'
  {A : Type} {R : A -> A -> Prop}
  (P : Type) (snil' : P) (scons' : A -> P -> P) :
  {f : slist R -> P |
    f snil = snil' /\
    forall (h : A) (t : slist R) (p : ok h t),
      f (scons h t p) = scons' h (f t)
  }.
Proof.
  destruct
  (
    ind
    A R
    (fun _ => P) (fun _ _ _ => True)
    snil' (fun h _ _ t _ => scons' h t)
    (fun _ => I) (fun _ _ _ _ _ _ _ => I)
  )
  as (f & g & H1 & H2 & H3 & H4).
  exists f. split.
    exact H1.
    exact H2.
Defined.

(** Możemy na przykład dość łatwo zdefiniować niezależny rekursor tylko dla
    [slist], nie odnoszący się w żaden sposób do [ok]. Widzimy jednak, że
    "programowanie" w taki aksjomatyczny sposób jest dość ciężkie - zamiast
    eleganckich dopasowań do wzorca musimy ręcznie wpisywać argumenty do
    reguły indukcyjnej. *)

Definition toList'
  {A : Type} {R : A -> A -> Prop} :
  {f : slist R -> list A |
    f snil = [] /\
    forall (h : A) (t : slist R) (p : ok h t),
      f (scons h t p) = h :: f t
  }.
Proof.
  exact (rec' (list A) [] cons).
Defined.

Definition toList
  {A : Type} {R : A -> A -> Prop} : slist R -> list A :=
    proj1_sig toList'.

(** Używanie takiego rekursora jest już dużo prostsze, co ilustruje powyższy
    przykład funkcji, która zapomina o tym, że lista jest posortowana i daje
    nam zwykłą listę.

    Przykładowe posortowane listy wyglądają tak: *)

Definition slist_01 : slist le :=
  scons 0
    (scons 1
      snil
      (ok_snil 1))
    (ok_scons 1 snil (ok_snil 1) 0 (le_S 0 0 (le_n 0))).

(** Niezbyt piękna, prawda? *)

Compute toList slist_01.

(** Utrapieniem jest też to, że nasza funkcja się nie oblicza. Jest tak, bo
    została zdefiniowana za pomocą reguły indukcji, która jest aksjomatem.
    Aksjomaty zaś, jak wiadomo, nie obliczają się.

    Wyniku powyższego wywołania nie będę nawet wklejał, gdyż jest naprawdę
    ohydny. *)

Lemma toList_slist_01_result :
  toList slist_01 = [0; 1].
Proof.
  unfold toList, slist_01.
  destruct toList' as (f & H1 & H2); cbn.
  rewrite 2!H2, H1. reflexivity.
Qed.

(** Najlepsze, co możemy osiągnąć, mając taką definicję, to udowodnienie, że
    jej wynik faktycznie jest taki, jak się spodziewamy. *)

(** **** Ćwiczenie *)

(** Zdefiniuj dla list posortowanych funkcję [slen], która liczy ich długość.
    Udowodnij oczywiste twierdzenie wiążące ze sobą [slen], [toList] oraz
    [length]. *)

(* begin hide *)

Definition slen'
  {A : Type} {R : A -> A -> Prop} :
  {f : slist R -> nat |
    f snil = 0 /\
    forall (h : A) (t : slist R) (p : ok h t),
      f (scons h t p) = S (f t)}.
Proof.
  exact (rec' nat 0 (fun _ n => S n)).
Defined.

Definition slen {A : Type} {R : A -> A -> Prop} : slist R -> nat :=
  proj1_sig slen'.

Lemma slen_toList_length :
  forall {A : Type} {R : A -> A -> Prop} (l : slist R),
    slen l = length (toList l).
Proof.
  intros A R.
  eapply (projT1 (
    ind A R (fun l => slen l = length (toList l))
      (fun _ _ _ => True)
      _ _
      (fun _ => I)
      (fun _ _ _ _ _ _ _ => I))).
  Unshelve.
  all: cbn; unfold slen, toList;
  destruct slen' as (f & Hf1 & Hf2), toList' as (g & Hg1 & Hg2); cbn.
    rewrite Hf1, Hg1. cbn. reflexivity.
    intros. rewrite Hf2, Hg2, H. cbn. reflexivity.
Qed.

(* end hide *)

(** **** Ćwiczenie *)

(** Udowodnij, że przykład faktycznie jest bez sensu: zdefiniuje relację
    [sorted : (A -> A -> Prop) -> list A -> Prop], gdzie [sorted R l]
    oznacza, że lista [l] jest posortowana według porządku [R]. Używając
    [sorted] zdefiniuj typ list posortowanych [slist' R], a następnie znajdź
    dwie funkcje [f : slist R -> slist' R] i [f : slist' R -> slist R],
    które są swoimi odwrotnościami. *)

(* begin hide *)

Inductive sorted {A : Type} (R : A -> A -> Prop) : list A -> Prop :=
| sorted_nil : sorted R []
| sorted_singl : forall x : A, sorted R [x]
| sorted_cons :
    forall (x y : A) (t : list A),
      R x y -> sorted R (y :: t) -> sorted R (x :: y :: t).

Arguments sorted_nil   {A R}.
Arguments sorted_singl {A R} _.
Arguments sorted_cons  {A R x y t} _ _.

Definition slist' {A : Type} (R : A -> A -> Prop) : Type :=
  {l : list A | sorted R l}.

Lemma toList_sorted :
  forall {A : Type} {R : A -> A -> Prop} (l : slist R),
    sorted R (toList l).
Proof.
  intros A R.
  refine (projT1 (ind
    A R
    (fun l => sorted R (toList l))
    (fun x t _ =>
      t = snil \/
      exists (h : A) (t' : slist R) (p : ok h t'),
        t = scons h t' p /\ R x h)
    _ _ _ _)).
  1-2: unfold toList; destruct toList' as (f & H1 & H2); cbn.
    rewrite H1. constructor.
    intros. rewrite H2. decompose [or ex and] H0; clear H0; subst.
      rewrite H1. constructor.
      rewrite H2 in *. constructor; assumption.
    intros. left. reflexivity.
    intros. decompose [or ex and] H1; clear H1; subst.
      right. exists h, snil, p. split; trivial.
      right. exists h, (scons x0 x1 x2), p. split; trivial.
Qed.

(** TODO *)

(* end hide *)

(** **** Ćwiczenie *)

(** Żeby przekonać się, że przykład był naprawdę bezsensowny, zdefiniuj
    rodzinę typów [blist : (A -> A -> Prop) -> A -> Type], gdzie elementami
    [blist R x] są listy posortowane, których elementy są [R]-większe od [x].
    Użyj [blist] do zdefiniowania typu [slist'' R], a następnie udowodnij,
    że [slist R] i [slist'' R] są sobie równoważne. *)

End ind_ind.

(** **** *)

(** Na koniec wypadałoby jeszcze wspomnieć, do czego tak naprawdę można w
    praktyce użyć indukcji-indukcji (definiowanie list posortowanych nie
    jest jedną z tych rzeczy, o czym przekonałeś się w ćwiczeniach). Otóż
    najciekawszym przykładem wydaje się być formalizacja teorii typów, czyli,
    parafrazując, implementacja Coqa w Coqu.

    Żeby się za to zabrać, musimy zdefiniować konteksty, typy i termy, a
    także relacje konwertowalności dla typów i termów. Są tutaj możliwe dwa
    podejścia:
    - Curry'ego (ang. Curry style lub mądrzej extrinsic style) - staramy
      się definiować wszystko osobno, a potem zdefiniować relacje "term x
      jest typu A w kontekście Γ", "typ A jest poprawnie sformowany w
      kontekście Γ" etc. Najważniejszą cechą tego sposobu jest to, że
      możemy tworzyć termy, którym nie da się przypisać żadnego typu oraz
      typy, które nie są poprawnie sformowane w żadnym kontekście.
    - Churcha (ang. Church style lub mądrzej intrinsic style) - definiujemy
      wszystko na raz w jednej wielkiej wzajemnej indukcji. Zamiastów
      typów definiujemy od razu predykat "typ A jest poprawnie sformowany
      w kontekście Γ", a zamiast termów definiujemy od razu relację
      "term x ma typ A w kontekście Γ". Parafrazując - wszystkie termy,
      które jesteśmy w stanie skonstruować, są poprawnie typowane (a
      wszystkie typy poprawnie sformowane w swoich kontekstach). *)

(** Zamiast tyle gadać zobaczmy, jak mogłoby to wyglądać w Coqu. Oczywiście
    będą to same nagłówki, bo podanie tutaj pełnej definicji byłoby mocno
    zaciemniającym przegięciem. *)

(*
Inductive Ctx : Type := ...

with Ty : Ctx -> Type := ...

with Term : forall Γ : Ctx, Ty Γ -> Type := ...

with TyConv : forall Γ : Ctx, Ty Γ -> Ty Γ -> Prop := ...

with
  TermConv :
    forall (Γ : Ctx) (A : Ty Γ),
      Term Γ A -> Term Γ A -> Prop := ...
*)

(** Nagłówki w tej definicji powinniśmy interpretować tak:
    - [Ctx] to typ reprezentujący konteksty.
    - [Ty] ma reprezentować typy, ale nie jest to typ, lecz rodzina typów
      indeksowana kontekstami - każdy typ jest typem w jakimś kontekście,
      np. [list A] jest typem w kontekście zawierającym [A : Type], ale
      nie jest typem w pustym kontekście.
    - [Term] ma reprezentować termy, ale nie jest to typ, lecz rodzina typów
      indeksowana kontekstami i typami - każdy term ma jakiś typ, a typy,
      jak już się rzekło, zawsze są typami w jakimś kontekście. Przykład:
      jeżeli [x] jest zmienną, to [cons x nil] jest typu [list A] w
      kontekście, w którym [x] jest typu [A], ale nie ma żadnego typu (i nie
      jest nawet poprawnym termem) w kontekście pustym ani w żadnym, w którym
      nie występuje [x].
    - [TyConv Γ A B] zachodzi, gdy typy [A] i [B] są konwertowalne, czyli
      obliczają się do tego samego (relacja taka jest potrzebna, gdyż w Coqu
      i ogólnie w teorii typów występować mogą takie typy jak [if true then
      nat else bool], który jest konwertowalny z [nat]). Jako się rzekło,
      typy zawsze występują w kontekście, więc konwertowalne mogą być też
      tylko w kontekście.
    - [TermConv Γ A x y] znaczy, że termy [x] i [y] są konwertowalne,
      np. [if true then 42 else 0] jest konwertowalne z [42]. Ponieważ każdy
      term ciągnie za sobą swój typ, [TermConv] ma jako indeks typ [A], a
      ponieważ typ ciągnie za sobą kontekst, indeksem [TermConv] jest także
      [Γ]. *)

(** Jak widać, indukcji-indukcji jest w powyższym przykładzie na pęczki -
    jest ona wręcz teleskopowa, gdyż [Ctx] jest indeksem [Ty], [Ctx] i [Ty]
    są indeksami [Term], a [Ctx], [Ty] i [Term] są indeksami [TermConv].

    Cóż, to by było na tyle w tym temacie.
    #<a class='link' href='https://www.sadistic.pl/lawa-oburzonych-vt22270.htm'>
    Ława oburzonych</a># wyraża w tym momencie swoje najwyższe oburzenie na brak
    indukcji-indukcji w Coqu.

    Jednak uszy do góry - istnieją już języki, które jakoś sobie radzą z
    indukcją-indukcją. Jednym z nich jest wspomniana we wstępie
    #<a class='link' href='https://agda.readthedocs.io/en/latest/'>Agda</a>#. *)

(** **** Ćwiczenie *)

(** Typ stert binarnych [BHeap R], gdzie [R : A -> A -> Prop] jest relacją
    porządku, składa się z drzew, które mogą być albo puste, albo być węzłem
    przechowującym wartość [v : A] wraz z dwoma poddrzewami [l r : BHeap R],
    przy czym [v] musi być [R]-większe od wszystkich elementów [l] oraz [r].

    Użyj indukcji-indukcji, żeby zdefiniować jednocześnie typ [BHeap R] oraz
    relację [ok], gdzie [ok v h] zachodzi, gdy [v] jest [R]-większe od
    wszystkich elementów [h].

    Najpierw napisz pseudodefinicję, a potem przetłumacz ją na odpowiedni
    zestaw aksjomatów.

    Następnie użyj swojej aksjomatycznej definicji, aby zdefiniować funkcję
    [mirror], która tworzy lustrzane odbicie sterty [h : BHeap R]. Wskazówka:
    prawdopodobnie nie uda ci się zdefiniować [mirror]. Zastanów się,
    dlaczego jest tak trudno. *)

(* begin hide *)

Module BHeap.

Fail

Inductive BHeap {A : Type} (R : A -> A -> Prop) : Type :=
| E : BHeap R
| N : forall (v : A) (l r : BHeap R), ok v l -> ok v r -> BHeap R

with ok {A : Type} {R : A -> A -> Prop} : A -> BHeap R -> Prop :=
| ok_E : forall v : A, ok v E
| ok_N :
    forall (v x : A) (l r : BHeap A) (pl : ok x l) (pr : ok x r),
      R x v -> ok v (N x l r pl pr).

Axioms
  (BHeap : forall {A : Type} (R : A -> A -> Prop), Type)
  (ok : forall {A : Type} {R : A -> A -> Prop}, A -> BHeap R -> Prop)
  (E : forall {A : Type} {R : A -> A -> Prop}, BHeap R)
  (N :
    forall
      {A : Type} {R : A -> A -> Prop}
      (v : A) (l r : BHeap R),
        ok v l -> ok v r -> BHeap R)
  (ok_E : forall {A : Type} {R : A -> A -> Prop} (v : A), ok v (@E _ R))
  (ok_N :
    forall
      {A : Type} {R : A -> A -> Prop}
      (v x : A) (l r : BHeap R) (pl : ok x l) (pr : ok x r),
        R x v -> ok v (N x l r pl pr))
  (ind : forall
    (A : Type) (R : A -> A -> Prop)
    (P : BHeap R -> Type)
    (Q : forall (v : A) (h : BHeap R), ok v h -> Type)
    (PE : P E)
    (PN : forall (v : A) (l r : BHeap R) (pl : ok v l) (pr : ok v r),
            P l -> P r -> Q v l pl -> Q v r pr -> P (N v l r pl pr))
    (Qok_E :
      forall v : A, Q v E (ok_E v))
    (Qok_N :
      forall
        (v x : A) (l r : BHeap R) (pl : ok x l) (pr : ok x r) (H : R x v),
          P l -> P r -> Q x l pl -> Q x r pr ->
            Q v (N x l r pl pr) (ok_N v x l r pl pr H)),
    {f : forall h : BHeap R, P h &
    {g : forall (v : A) (h : BHeap R) (p : ok v h), Q v h p |
      f E = PE /\
      (forall (v : A) (l r : BHeap R) (pl : ok v l) (pr : ok v r),
        f (N v l r pl pr) =
        PN v l r pl pr (f l) (f r) (g v l pl) (g v r pr)) /\
      (forall v : A, g v E (ok_E v) = Qok_E v) /\
      (forall
        (v x : A) (l r : BHeap R) (pl : ok x l) (pr : ok x r) (H : R x v),
          g v (N x l r pl pr) (ok_N v x l r pl pr H) =
          Qok_N v x l r pl pr H (f l) (f r) (g x l pl) (g x r pr))
    }}).

(*
Definition mirror
  {A : Type} {R : A -> A -> Prop}
  :
  {f : BHeap R -> BHeap R &
  {g : forall {v : A} {h : BHeap R}, ok v h -> ok v (f h) |
    f E = E /\
    (forall (v : A) (l r : BHeap R) (pl : ok v l) (pr : ok v r),
      f (N v l r pl pr) = N v (f r) (f l) (g v r pr) (g v l pl)) /\
    (forall v : A, g v E (ok_E v) = ok_E v)
  }}.
Proof.
  Check (
    ind
      A R
      (fun _ => BHeap R)). 
      (fun _ _ _ => True)
      E (fun v _ _ _ _ l' r' pl' pr' => N v r' l' pr' pl')
      (fun _ => I) (fun _ _ _ _ _ _ _ _ _ _ _ => I)
  ).
*)

End BHeap.

(* end hide *)

(** **** Ćwiczenie *)

(** Typ drzew wyszukiwań binarnych [BST R], gdzie [R : A -> A -> Prop] jest
    relacją porządku, składa się z drzew, które mogą być albo puste, albo być
    węzłem przechowującym wartość [v : A] wraz z dwoma poddrzewami
    [l r : BST R], przy czym [v] musi być [R]-większe od wszystkich elemtnów
    [l] oraz [R]-mniejsze od wszystkich elementów [r].

    Użyj indukcji-indukcji, żeby zdefiniować jednocześnie typ [BST R] wraz
    z odpowiednimi relacjami zapewniającymi poprawność konstrukcji węzła.
    Wypróbuj trzy podejścia:
    - jest jedna relacja, [oklr], gdzie [oklr v l r] oznacza, że z [v], [l] i
      [r] można zrobić węzeł
    - są dwie relacje, [okl] i [okr], gdzie [okl v l] oznacza, że [v] jest
      [R]-większe od wszystkich elementów [l], zaś [okr v r], że [v] jest
      [R]-mniejsze od wszystkich elementów [r]
    - jest jedna relacja, [ok], gdzie [ok v t] oznacza, że [v] jest
      [R]-mniejsze od wszystkich elementów [t] *)

(** Najpierw napisz pseudodefinicję, a potem przetłumacz ją na odpowiedni
    zestaw aksjomatów.

    Następnie użyj swojej aksjomatycznej definicji, aby zdefiniować funkcję
    [mirror], która tworzy lustrzane odbicie drzewa [t : BST R]. Wskazówka:
    dość możliwe, że ci się nie uda. *)

(* begin hide *)

(** TODO: przetłumacz na odpowiedni zestaw aksjomatów, zdefiniuj mirror *)

Module BST.

Fail

Inductive BST {A : Type} (R : A -> A -> Prop) : Type :=
| E : BST R
| N : forall (v : A) (l r : BST R), ok v l r -> BST R

with ok {A : Type} {R : A -> A -> Prop} : A -> BST R -> BST R -> Prop :=
| ok_EE : forall v : A, ok v E E
| ok_EN :
    forall (v vl : A) (ll lr : BST R),
      R vl v -> ok v (N vl ll lr) E
| ok_NE :
    forall (v vr : A) (rl rr : BST R),
      R v vr -> ok v E (N vr rl rr)
| ok_NN :
    forall (v vl vr : A) (ll lr rl rr : BST R),
      R vl v -> R v vr -> ok v (N vl ll lr) (N vr rl rr).

Fail

Inductive BST {A : Type} (R : A -> A -> Prop) : Type :=
| E : BST R
| N : forall (v : A) (l r : BST R), okl v l -> okr v r -> BST R

with okl {A : Type} {R : A -> A -> Prop} : A -> BST R -> Prop :=
| okl_E : forall v : A, okl v E
| okl_N :
    forall (v vl : A) (ll lr : BST R),
      R vl v -> okl v (N vl ll lr)

with okr {A : Type} {R : A -> A -> Prop} : A -> BST R -> Prop :=
| okr_E : forall v : V, okr v E
| okr_N :
    forall (v vr : A) (rl rr : BST R),
      R v vr -> okr v (N vr rl rr).

Definition inv {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
  fun x y => R y x.

Fail

Inductive BST {A : Type} (R : A -> A -> Prop) : Type :=
| E : BST R
| N : forall (v : A) (l r : BST R),
        @ok A R v l -> @ok A (inv R) v r -> BST R

with ok {A : Type} {R : A -> A -> Prop} : A -> BST R -> Prop :=
| ok_E : forall v : A, ok v E
| ok_N : forall (v x : A) (l r : BST R),
           R x v -> ok v (N x l r).

End BST.

(* end hide *)

(** ** Indukcja-rekursja *)

Module ind_rec.

(** A oto kolejny potfur do naszej kolekcji: indukcja-rekursja. Nazwa, choć
    brzmi tak głupio, jak "indukcja-indukcja", niesie ze sobą jednak dużo
    więcej wyobraźni: indukcja-rekursja pozwala nam jednocześnie definiować
    typy induktywne oraz operujące na nich funkcje rekurencyjne.

    Co to dokładnie znaczy? Dotychczas nasz modus operandi wyglądał tak, że
    najpierw definiowaliśmy jakiś typ induktywny, a potem przez rekursję
    definiowaliśmy operujące na nim funkcje, np:
    - najpierw zdefiniowaliśmy typ [nat], a potem dodawanie, mnożenie etc.
    - najpierw zdefiniowaliśmy typ [list A], a potem [app], [rev] etc. *)

(** Dlaczego mielibyśmy chcieć definiować typ i funkcję jednocześnie? Dla
    tego samego, co zawsze, czyli zależności - indukcja-rekursja pozwala,
    żeby definicja typu odnosiła się do funkcji, która to z kolei jest
    zdefiniowana przez rekursję strukturalną po argumencie o tym typie.

    Zobaczmy dobrze nam już znany bezsensowny przykład, czyli listy
    posortowane, tym razem zaimplementowane za pomocą indukcji-rekursji. *)

(*
Inductive slist {A : Type} (R : A -> A -> bool) : Type :=
| snil : slist R
| scons : forall (h : A) (t : slist R), ok h t = true -> slist R

with

Definition ok
  {A : Type} {R : A -> A -> bool} (x : A) (t : slist R) : bool :=
match t with
| snil => true
| scons h _ _ => R x h
end.
*)

(** Coq niestety nie wspiera indukcji-rekursji, a próba napisania powyższej
    definicji kończy się błędem składni, przy którym nie pomaga nawet komenda
    [Fail]. Podobnie jak poprzednio, pomożemy sobie za pomocą aksjomatów,
    jednak najpierw prześledźmy definicję.

    Typ [slist R] działa następująco:
    - [R] to jakiś porządek. Zauważ, że tym razem [R : A -> A -> bool], a
      więc porządek jest reprezentowany przez funkcję, która go rozstrzyga
    - [snil] to lista pusta
    - [scons h t p] to lista z głową [h] i ogonem [t], zaś [p : ok h t = true]
      to dowód na to, że dostawienie [h] przed [t] daje listę posortowaną. *)

(** Tym razem jednak [ok] nie jest relacją, lecz funkcją zwracającą [bool],
    która działa następująco:
    - dla [snil] zwróć [true] - każde [x : A] można dostawić do listy pustej
    - dla [scons h _ _] zwróć wynik porównania [x] z [h] *)

(** Istotą mechanizmu indukcji-rekursji w tym przykładzie jest to, że [scons]
    wymaga dowodu na to, że funkcja [ok] zwraca [true], podczas gdy funkcja
    ta jest zdefiniowana przez rekursję strukturalną po argumencie typu
    [slist R].

    Użycie indukkcji-rekursji do zaimplementowania [slist] ma swoje zalety:
    dla konkretnych list (złożonych ze stałych, a nie ze zmiennych) dowody
    [ok h t = true] będą postaci [eq_refl], bo [ok] po prostu obliczy się
    do [true]. W przypadku indukcji-indukcji dowody na [ok h t] były całkiem
    sporych rozmiarów drzewami. Innymi słowy, udało nam się zastąpić część
    termu obliczeniami. Ten intrygujący motyw jeszcze się w przyszłości
    pojawi, gdy omawiać będziemy dowód przez reflekcję.

    Dosyć gadania! Zobaczmy, jak zakodować powyższą definicję za pomocą
    aksjomatów. *)

Axioms
  (slist : forall {A : Type}, (A -> A -> bool) -> Type)
  (ok :
    forall {A : Type} {R : A -> A -> bool}, A -> slist R -> bool)
  (snil :
    forall {A : Type} {R : A -> A -> bool}, slist R)
  (scons :
    forall
      {A : Type} {R : A -> A -> bool}
      (h : A) (t : slist R),
        ok h t = true -> slist R)
  (ok_snil :
    forall {A : Type} {R : A -> A -> bool} (x : A),
      ok x (@snil _ R) = true)
  (ok_scons :
    forall
      {A : Type} {R : A -> A -> bool}
      (x h : A) (t : slist R) (p : ok h t = true),
        ok x (scons h t p) = R x h).

(** Najpierw musimy zadeklarować [slist], a następnie [ok], gdyż typ [ok]
    zależy od [slist]. Następnym krokiem jest zadeklarowanie konstruktorów
    [slist], a później równań definiujących funkcję [ok] - koniecznie w tej
    kolejności, gdyż równania zależą od konstruktorów.

    Jak widać, aksjomaty są bardzo proste i sprowadzają się do przepisania
    powyższej definicji odrzuconej przez Coqa. *)

Axiom
  ind : forall
    (A : Type) (R : A -> A -> bool)
    (P : slist R -> Type)
    (Psnil : P snil)
    (Pscons :
      forall (h : A) (t : slist R) (p : ok h t = true),
        P t -> P (scons h t p)),
    {f : forall l : slist R, P l |
      f snil = Psnil /\
      (forall (h : A) (t : slist R) (p : ok h t = true),
        f (scons h t p) = Pscons h t p (f t))}.

(** Innym zyskiem z użycia indukcji-rekursji jest postać reguły indukcyjnej.
    Jest ona dużo prostsza, niż w przypadku indukcji-indukcji, gdyż teraz
    definiujemy tylko jeden typ, zaś towarzysząca mu funkcja nie wymaga w
    regule niczego specjalnego - po prostu pojawia się w niej tam, gdzie
    spodziewamy się jej po definicji [slist], ale nie robi niczego
    ponad to. Może to sugerować, że zamiast indukcji-indukcji, o ile to
    możliwe, lepiej jest używać indukcji-rekursji, a predykaty i relacje
    definiować przez rekursję.

    Powyższą regułę możemy odczytać następująco:
    - [A : Type] i [R : A -> A -> bool] to parametry [slist], więc muszą się
      pojawić
    - [P : slist R -> Type] to przeciwdziedzina funkcji definiowanej za
      pomocą reguły
    - [Psnil] to wynik funkcji dla [snil]
    - [Pscons] produkuje wynik funkcji dla [scons h t p] z hipotezy
      indukcyjnej/wywołania rekurencyjnego dla [t]
    - [f : forall l : slist R, P l] to funkcja zdefiniowana przez regułę,
      zaś równania formalizują to, co zostało napisane powyżej o [Psnil]
      i [Pscons] *)

(** Termy induktywno-rekurencyjnego [slist R] wyglądają następująco
    (najpierw definiujemy sobie funkcję rozstrzygającą standardowy
    porządek na liczbach naturalnych): *)

Fixpoint leb (n m : nat) : bool :=
match n, m with
| 0, _ => true
| _, 0 => false
| S n', S m' => leb n' m'
end.

Definition slist_01 : slist leb :=
  scons 0
    (scons 1
      snil
      (ok_snil 1))
    (ok_scons 0 1 snil (ok_snil 1)).

(** Nie wygląda wiele lepiej od poprzedniej, induktywno-induktywnej wersji,
    prawda? Ta rażąca kiepskość nie jest jednak zasługą indukcji-rekursji,
    lecz kodowania za pomocą aksjomatów - funkcja [ok] się nie oblicza,
    więc zamiast [eq_refl] musimy używać aksjomatów [ok_snil] i [ok_scons].

    W tym momencie znów wkracza ława oburzonych i wyraża swoje oburzenie na
    fakt, że Coq nie wspiera indukcji-rekursji (ale Agda już tak). Gdyby
    [Coq] wspierał indukcję-rekursję, to ten term wyglądałby tak: *)

Fail Definition slist_01 : slist leb :=
  scons 0 (scons 1 snil eq_refl) eq_refl.

(** Dużo lepiej, prawda? Na koniec zobaczmy, jak zdefiniować funkcję
    zapominającą o fakcie, że lista jest posortowana. *)

Definition toList'
  {A : Type} {R : A -> A -> bool} :
  {f : slist R -> list A |
    f snil = [] /\
    forall (h : A) (t : slist R) (p : ok h t = true),
      f (scons h t p) = h :: f t
  }.
Proof.
  exact (ind A R (fun _ => list A) [] (fun h _ _ r => h :: r)).
Defined.

Definition toList
  {A : Type} {R : A -> A -> bool} : slist R -> list A :=
    proj1_sig toList'.

(** Ponownie jest to dużo prostsze, niż w przypadku indukcji-indukcji -
    wprawdzie wciąż musimy ręcznie wpisywać termy do reguły indukcji,
    ale dzięki prostocie reguły jest to znacznie łatwiejsze. Alternatywnie:
    udało nam się zaoszczędzić trochę czasu na definiowaniu reguły rekursji,
    co w przypadku indukcji-indukcji było niemal konieczne, żeby nie
    zwariować. *)

Lemma toList_slist_01_result :
  toList slist_01 = [0; 1].
Proof.
  unfold toList, slist_01.
  destruct toList' as (f & H1 & H2).
  cbn. rewrite 2!H2, H1. reflexivity.
Qed.

(** Udowodnienie, że nasza funkcja daje taki wynik jak chcieliśmy, jest
    równie proste jak poprzednio. *)

(** **** Ćwiczenie *)

(** Zdefiniuj dla list posortowanych funkcję [slen], która liczy ich długość.
    Udowodnij oczywiste twierdzenie wiążące ze sobą [slen], [toList] oraz
    [length]. Czy było łatwiej, niż w przypadku indukcji-indukcji? *)

(* begin hide *)

Definition slen'
  {A : Type} {R : A -> A -> bool} :
  {f : slist R -> nat |
    f snil = 0 /\
    forall (h : A) (t : slist R) (p : ok h t = true),
      f (scons h t p) = S (f t)}.
Proof.
  exact (ind A R (fun _ => nat) 0 (fun _ _ _ n => S n)).
Defined.

Definition slen {A : Type} {R : A -> A -> bool} : slist R -> nat :=
  proj1_sig slen'.

Lemma slen_toList_length :
  forall {A : Type} {R : A -> A -> bool} (l : slist R),
    slen l = length (toList l).
Proof.
  intros A R.
  eapply (proj1_sig
    (ind A R (fun l : slist R => slen l = length (toList l)) _ _)).
  Unshelve.
  all: cbn; unfold slen, toList;
  destruct slen' as (f & Hf1 & Hf2), toList' as (g & Hg1 & Hg2); cbn.
    rewrite Hf1, Hg1. cbn. reflexivity.
    intros. rewrite Hf2, Hg2, H. cbn. reflexivity.
Qed.

(** Czy było łatwiej, niż zrobić to samo indukcją-indukcją? Tak, ale tylko
    troszkę. *)

(* end hide *)

End ind_rec.

(** **** Ćwiczenie *)

(** No cóż, jeszcze raz to samo. Zdefiniuj za pomocą indukcji-rekursji
    jednocześnie typ stert binarnych [BHeap R], gdzie [R : A -> A -> bool]
    rozstrzyga porządek, i funkcję [ok : A -> BHeap R -> bool], gdzie
    [ok x h = true], gdy stertę [h] można podczepić pod element [x].

    Najpierw napisz pseudodefinicję, a potem przetłumacz ją na odpowiedni
    zestaw aksjomatów.

    Następnie użyj swojej aksjomatycznej definicji, aby zdefiniować funkcję
    [mirror], która tworzy lustrzane odbicie sterty [h : BHeap R]. Wskazówka:
    tym razem powinno ci się udać.

    Porównaj induktywno-rekurencyjną implementację [BHeap R] i [ok] z
    implementacją przez indukcję-indukcję. Która jest bardziej ogólna?
    Która jest "lżejsza"? Która jest lepsza? *)

(* begin hide *)
Module BHeap'.

(*
Inductive BHeap {A : Type} (R : A -> A -> bool) : Type :=
| E : BHeap R
| N : forall (v : A) (l r : BHeap R),
        ok R v l = true -> ok R v r = true -> BHeap R

with ok {A : Type} (R : A -> A -> bool) (x : A) (h : BHeap R) : bool :=
match h with
| E => true
| N v l r _ _ => R x v
end.
*)

Axioms
  (BHeap : forall {A : Type} (R : A -> A -> bool), Type)
  (ok : forall {A : Type} (R : A -> A -> bool) (x : A) (h : BHeap R), bool)
  (E : forall {A : Type} {R : A -> A -> bool}, BHeap R)
  (N :
    forall {A : Type} {R : A -> A -> bool} (v : A) (l r : BHeap R),
      ok R v l = true -> ok R v r = true -> BHeap R)
  (ok_E :
    forall {A : Type} {R : A -> A -> bool} (x : A),
      ok R x E = true)
  (ok_N :
    forall
      {A : Type} {R : A -> A -> bool}
      (x v : A) (l r : BHeap R)
      (eql : ok R v l = true) (eqr : ok R v r = true),
        ok R x (N v l r eql eqr) = R x v)
  (ind :
    forall
      {A : Type} {R : A -> A -> bool}
      (P : BHeap R -> Type)
      (P_E : P E)
      (P_N :
        forall
          (v : A) (l r : BHeap R)
          (eql : ok R v l = true) (eqr : ok R v r = true),
            P l -> P r -> P (N v l r eql eqr)),
      {f : forall h : BHeap R, P h |
        f E = P_E /\
        (forall
          (v : A) (l r : BHeap R)
          (eql : ok R v l = true) (eqr : ok R v r = true),
            f (N v l r eql eqr) = P_N v l r eql eqr (f l) (f r))}).

Definition mirror
  {A : Type} {R : A -> A -> bool} (h : BHeap R) :
  {h' : BHeap R | forall x : A, ok R x h' = ok R x h}.
Proof.
  revert h.
  apply (@ind A R (fun h : BHeap R =>
    {h' : BHeap R | forall x : A, ok R x h' = ok R x h}
  )).
    exists E. reflexivity.
    intros * [l' IHl'] [r' IHr']. eexists (N v r' l' _ _). Unshelve.
      intros. rewrite !ok_N. reflexivity.
      rewrite IHr'. assumption.
      rewrite IHl'. assumption.
Defined.

End BHeap'.
(* end hide *)

(** **** Ćwiczenie *)

(** No cóż, jeszcze raz to samo. Zdefiniuj za pomocą indukcji-rekursji
    jednocześnie typ drzew wyszukiwań binarnych [BST R], gdzie
    [R : A -> A -> bool] rozstrzyga porządek, oraz funkcje
    [oklr]/[okl] i [okr]/[ok], które dbają o odpowiednie warunki (wybierz
    tylko jeden wariant z trzech, które testowałeś w tamtym zadaniu).

    Najpierw napisz pseudodefinicję, a potem przetłumacz ją na odpowiedni
    zestaw aksjomatów.

    Następnie użyj swojej aksjomatycznej definicji, aby zdefiniować funkcję
    [mirror], która tworzy lustrzane odbicie drzewa [t : BST R]. Wskazówka:
    tym razem powinno ci się udać.

    Porównaj induktywno-rekurencyjną implementację [BST R] z implementacją
    przez indukcję-indukcję. Która jest bardziej ogólna? Która jest
    "lżejsza"? Która jest lepsza? *)

(* begin hide *)
Module BST'.

(** TODO: definicja chyba jest źle... *)

(*
Inductive BST {A : Type} (R : A -> A -> bool) : Type :=
| E : BST R
| N : forall (v : A) (l r : BST R),
        okl R v l = true -> okr R v l = true -> BST R

with okl {A : Type} (R : A -> A -> bool) (x : A) (t : BST R) : bool :=
match t with
| E => true
| N v _ _ _ _ => R x v
end

with okr {A : Type} (R : A -> A -> bool) (x : A) (t : BST R) : bool :=
match t with
| E => true
| N v _ _ _ _ => negb (R x v)
*)

Axioms
  (BST : forall {A : Type} (R : A -> A -> bool), Type)
  (okl : forall {A : Type} {R : A -> A -> bool} (x : A) (t : BST R), bool)
  (okr : forall {A : Type} {R : A -> A -> bool} (x : A) (t : BST R), bool)
  (E : forall {A : Type} {R : A -> A -> bool}, BST R)
  (N :
    forall
      {A : Type} {R : A -> A -> bool}
      (v : A)
      (l r : BST R)
      (eql : okl v l = true) (eqr : okr v r = true), BST R)
  (okl_E :
    forall {A : Type} {R : A -> A -> bool} (x : A),
      okl x (@E A R) = true)
  (okl_N :
    forall
      {A : Type} {R : A -> A -> bool}
      (x v : A) (l r : BST R)
      (eql : okl v l = true) (eqr : okr v r = true),
        okl x (N v l r eql eqr) = R x v)
  (okr_E :
    forall {A : Type} {R : A -> A -> bool} (x : A),
      okr x (@E A R) = true)
  (okr_N :
    forall
      {A : Type} {R : A -> A -> bool}
      (x v : A) (l r : BST R)
      (eql : okl v l = true) (eqr : okr v r = true),
        okr x (N v l r eql eqr) = negb (R x v))
  (ind :
    forall
      {A : Type} {R : A -> A -> bool}
      (P : BST R -> Type)
      (P_E : P E)
      (P_N :
        forall
          (v : A) (l r : BST R)
          (eql : okl v l = true) (eqr : okr v r = true),
            P l -> P r -> P (N v l r eql eqr)),
      {f : forall t : BST R, P t |
        f E = P_E /\
        forall
          (v : A) (l r : BST R)
          (eql : okl v l = true) (eqr : okr v r = true),
            f (N v l r eql eqr) = P_N v l r eql eqr (f l) (f r)
      }
  ).

Definition mirror
  {A : Type} {R : A -> A -> bool} (t : BST R) :
    {t' : BST (fun x y : A => negb (R x y)) |
      (forall x : A, okl x t' = okr x t) /\
      (forall x : A, okr x t' = okl x t)}.
Proof.
  revert t.
  apply (@ind A R (fun t : BST R =>
    {t' : BST (fun x y : A => negb (R x y)) |
      (forall x : A, okl x t' = okr x t) /\
      (forall x : A, okr x t' = okl x t)
    }
  )).
    exists E. split; intro; rewrite !okl_E, !okr_E; reflexivity.
    intros v l r eql eqr (l' & IHl1 & IHl2) (r' & IHr1 & IHr2).
      eexists (N v r' l' _ _). Unshelve.
        split; intro; rewrite okl_N, okr_N.
          reflexivity.
          destruct (R x v); reflexivity.
        rewrite IHr1, eqr. reflexivity.
        rewrite IHl2, eql. reflexivity.
Defined.

End BST'.
(* end hide *)

(** Podobnie jak poprzednio, pojawia się pytanie: do czego w praktyce
    można użyć indukcji-rekursji (poza rzecz jasna głupimi strukturami
    danych, jak listy posortowane)? W świerszczykach dla bystrzaków
    (czyli tzw. "literaturze naukowej") przewija się głównie jeden (ale
    jakże użyteczny) pomysł: uniwersa.

    Czym są uniwersa i co mają wspólnego z indukcją-rekursją? Najlepiej
    będzie przekonać się na przykładzie programowania generycznego: *)

(** **** Ćwiczenie (zdecydowanie za trudne) *)

(** Zaimplementuj generyczną funkcję [flatten], która spłaszcza dowolnie
    zagnieżdżone listy list do jednej, płaskiej listy.

    [flatten 5 = [5]]

    [flatten [1; 2; 3] = [1; 2; 3]]

    [flatten [[1]; [2]; [3]] = [1; 2; 3]]

    [flatten [[[1; 2]]; [[3]]; [[4; 5]; [6]]] = [1; 2; 3; 4; 5; 6]] *)

(** Trudne, prawda? Ale robialne, a robi się to tak.

    W typach argumentów [flatten] na powyższym przykładzie widać pewien
    wzorzec: są to kolejno [nat], [list nat], [list (list nat)],
    [list (list (list nat))] i tak dalej. Możemy ten "wzorzec" bez problemu
    opisać za pomocą następującego typu: *)

Inductive FlattenType : Type :=
| Nat : FlattenType
| List : FlattenType -> FlattenType.

(** Żeby było śmieszniej, [FlattenType] to dokładnie to samo co [nat], ale
    przemilczmy to. Co dalej? Możemy myśleć o elementach [FlattenType] jak
    o kodach prawdziwych typów, a skoro są to kody, to można też napisać
    funkcję dekodującą: *)

Fixpoint decode (t : FlattenType) : Type :=
match t with
| Nat => nat
| List t' => list (decode t')
end.

(** [decode] każdemu kodowi przyporządkowuje odpowiadający mu typ. O
    kodach możemy myśleć jak o nazwach - [Nat] to nazwa [nat], zaś
    [List t'] to nazwa typu [list (decode t')], np. [List (List Nat)]
    to nazwa typu [list (list nat)].

    Para [(FlattenType, decode)] jest przykładem uniwersum.

    Uniwersum to, najprościej pisząc, worek, który zawiera jakieś typy.
    Formalnie uniwersum składa się z typu kodów (czyli "nazw" typów) oraz
    funkcji dekodującej, która przyporządkowuje kodom prawdziwe typy.

    Programowanie generyczne to programowanie funkcji, które operują na
    kolekcjach typów o dowolnych kształtach, czyli na uniwersach właśnie.
    Generyczność od polimorfizmu różni się tym, że funkcja polimorficzna
    działa dla dowolnego typu, zaś generyczna - tylko dla typu o pasującym
    kształcie.

    Jak dokończyć implementację funkcji [flatten]? Kluczowe jest zauważenie,
    że możemy zdefiniować [flatten] przez rekursję strutkuralną po argumencie
    domyślnym typu [FlattenType]. Ostatni problem to jak zrobić, żeby Coq sam
    zgadywał kod danego typu - dowiemy się tego w rozdziale o klasach.

    Co to wszystko ma wspólnego z uniwersami? Ano, jeżeli chcemy definiować
    bardzo zaawansowane funkcje generyczne, musimy mieć do dyspozycji bardzo
    potężne uniwersa i to właśnie je zapewnia nam indukcja-rekursja. Ponieważ
    w powyższym przykładzie generyczność nie była zbyt wyrafinowana, nie było
    potrzeby używania indukcji-rekursji, jednak uszy do góry: przykład nieco
    bardziej skomplikowanego uniwersum pojawi się jeszcze w tym rozdziale. *)

(** **** Ćwiczenie *)

(** Nieco podchwytliwe zadanie: zdefiniuj uniwersum funkcji [nat -> nat],
    [nat -> (nat -> nat)], [(nat -> nat) -> nat],
    [(nat -> nat) -> (nat -> nat)] i tak dalej, dowolnie zagnieżdżonych.

    Zagadka: czy potrzebna jest nam indukcja-rekursja? *)

(** ** Indeksowana indukcja-rekursja *)

(** Za siedmioma górami, za siedmioma lasami, za siedmioma rzekami, za
    siedmioma budkami telefonicznymi, nawet za indukcją-rekursją (choć
    tylko o kroczek) leży indeksowana indukcja-rekursja, czyli połączenie
    indukcji-rekursji oraz indeksowanych rodzin typów.

    Jako, że w porównaniu do zwykłej indukcji-rekursji nie ma tu za wiele
    innowacyjności, przejdźmy od razu do przykładu przydatnej techniki,
    którą nasza tytułowa bohaterka umożliwia, a zwie się on metodą
    induktywnej dziedziny.

    Pod tą nazwą kryje się sposób definiowania funkcji, pozwalający oddzielić
    samą definicję od dowodu jej terminacji. Jeżeli ten opis nic ci nie mówi,
    nie martw się: dotychczas definiowaliśmy tylko tak prymitywne funkcje, że
    tego typu fikołki nie były nam potrzebne.

    Metoda induktywnej dziedziny polega na tym, żeby zamiast funkcji
    [f : A -> B], która nie jest strukturalnie rekurencyjna (na co Coq
    nie pozwala) napisać funkcję [f : forall x : A, D x -> B], gdzie
    [D : A -> Type] jest "predykatem dziedziny", który sprawia, że dziwna
    rekursja z oryginalnej definicji [f] staje się rekursją strukturalną
    po dowodzie [D x]. Żeby zdefiniować oryginalne [f : A -> B] wystarczy
    udowodnić, że każde [x : A] spełnia predykat dziedziny.

    Co to wszystko ma wspólnego z indeksowaną indukcją-rekursją? Już piszę.
    Otóż metoda ta nie wymaga w ogólności indukcji-rekursji - ta staje się
    potrzebna dopiero, gdy walczymy z bardzo złośliwymi funkcjami, czyli
    takimi, w których rekursja jest zagnieżdżona, tzn. robimy wywołanie
    rekurencyjne na wyniku poprzedniego wywołania rekurencyjnego.

    Predykat dziedziny dla takiej funkcji musi zawierać konstruktor w stylu
    "jeżeli wynik wywołania rekurencyjnego na x należy do dziedziny, to x też
    należy do dziedziny".To właśnie tu ujawnia się indukcja-rekursja: żeby
    zdefiniować predykat dziedziny, musimy odwołać się do funkcji (żeby móc
    powiedzieć coś o wyniku wywołania rekurencyjnego), a żeby zdefiniować
    funkcję, musimy mieć predykat dziedziny.

    Brzmi skomplikowanie? Jeżeli czegoś nie rozumiesz, to jesteś debi...
    a nie, czekaj. Jeżeli czegoś nie rozumiesz, to nie martw się: powyższy
    przykład miał na celu jedynie zilustrować jakieś praktyczne zastosowanie
    indeksowanej indukcji-rekursji. Do metody induktywnej dziedziny powrócimy
    w kolejnym rozdziale. Pokażemy, jak wyeliminować z niej indukcję-rekursję,
    tak żeby uzyskane za jej pomocą definicje można było odpalać w Coqu.
    Zobaczymy też, jakimi sposobami dowodzić, że każdy element dziedziny
    spełnia predykat dziedziny, co pozwoli nam odzyskać oryginalną definicję
    funkcji, a także dowiemy się, jak z "predykatu" o typie [D : A -> Type]
    zrobić prawdziwy predykat [D : A -> Prop]. *)

(** ** Indukcja-indukcja-rekursja *)

(** Ufff... przebrnęliśmy przez indukcję-indukcję i (indeksowaną)
    indukcję-rekursję. Czy mogą istnieć jeszcze potężniejsze i bardziej
    innowacyjne sposoby definiowania typów przez indukcję?

    Ależ oczywiście. Jest nim... uwaga uwaga, niespodzianka...
    indukcja-indukcja-rekursja, która jest nie tylko strasznym
    potfurem, ale też powinna dostać Oskara za najlepszą nazwę.

    Chodzi tu oczywiście o połączenie indukcji-indukcji i indukcji-rekursji:
    możemy jednocześnie zdefiniować jakiś typ [A], rodzinę typów [B]
    indeksowaną przez [A] oraz operujące na nich funkcje, do których
    konstruktory [A] i [B] mogą się odwoływać.

    Nie ma tu jakiejś wielkiej filozofii: wszystkiego, co powinieneś wiedzieć
    o indukcji-indukcji-rekursji, dowiedziałeś się już z dwóch poprzednich
    podrozdziałów. Nie muszę chyba dodawać, że ława oburzonych jest oburzona
    faktem, że Coq nie wspiera indukcji-indukcji-rekursji.

    Rodzi się jednak to samo super poważne pytanie co zawsze, czyli do czego
    można tego tałatajstwa użyć? Przez całkiem długi czas nie miałem pomysłu,
    ale okazuje się, że jest jedno takie zastosowanie i w sumie narzuca się
    ono samo.

    Przypomnij sobie metodę induktywno-rekurencyjnej dziedziny, czyli jedno
    ze sztandarowych zastosowań indeksowanej indukcji-rekursji. Zaczynamy od
    typu [I : Type], na którym chcemy zdefiniować funkcję o niestandardowym
    kształcie rekursji. W tym celu definiujemy dziedzinę [D : I -> Type]
    wraz z funkcją [f : forall i : I, D i -> R].

    Zauważmy jaki jest związek typu [I] z funkcją [f]: najpierw jest typ,
    potem funkcja. Co jednak, gdy musimy [I] oraz [f] zdefiniować razem za
    pomocą indukcji-rekursji? Wtedy [f] może być zdefiniowane jedynie za
    pomocą rekursji strukturalnej po [I], co wyklucza rekursję o fikuśnym
    kształcie...

    I tu wchodzi indukcja-indukcja-rekursja, cała na biało. Możemy użyć
    jej w taki sposób, że definiujemy jednocześnie:
    - typ [I], który odnosi się do funkcji [f]
    - predykat dziedziny [D : I -> Type], który jest indeksowany przez [I]
    - funkcję [f], która zdefiniowana jest przez rekursję strukturalną po
      dowodzie należenia do dziedziny

    Jak widać, typ zależy od funkcji, funkcja od predykatu, a predykat od
    typu i koło się zamyka.

    Następuje jednak skądinąd uzasadnione pytanie: czy faktycznie istnieje
    jakaś sytuacja, w której powyższy schemat działania jest tym słusznym?
    Odpowiedź póki co może być tylko jedna: nie wiem, ale się domyślam. *)

(** ** Wyższe Typy Induktywne (TODO) *)

(** Tutaj jakieś nie-homotopiczne przykłady, np. pary nieuporządkowane, zbiory,
    albo coś w ten deseń. *)