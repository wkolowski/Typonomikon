(** * G9: Stary rozdział o zaawansowanej indukcji [TODO] *)

(** W tym rozdziale będzie o mechanizmach definiowania typów induktywnych,
    które nie są dostępne w Coqu i w związku z tym musimy uciekać się do
    różnych sztuczek, żeby je zasymulować. *)

(** * Wyższe czary *)

(** Najwyższy czas nauczyć się czegoś tak zaawansowanego, że nawet w Coqu
    (pełnym przecież dziwnych rzeczy) tego nie ma i nie zapowiada się na
    to, że będzie. Mam tu na myśli mechanizmy takie jak indukcja-indukcja,
    indukcja-rekursja oraz indukcja-indukcja-rekursja (jak widać, w świecie
    poważnych uczonych, podobnie jak świecie Goebbelsa, im więcej razy
    powtórzy się dane słowo, tym więcej płynie z niego mocy). *)

(** * Przypomnienie *)

(** Zanim jednak wyjaśnimy, co to za stwory, przypomnijmy sobie różne, coraz
    bardziej innowacyjne sposoby definiowania przez indukcję oraz dowiedzmy
    się, jak sformułować i udowodnić wynikające z nich reguły rekursji oraz
    indukcji. *)

Unset Elimination Schemes.

(** Powyższa komenda mówi Coqowi, żeby nie generował automatycznie reguł
    indukcji. Przyda nam się ona, by uniknąć konfliktów nazw z regułami,
    które będziemy pisać ręcznie. *)

(** ** Enumeracje *)

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

(** ** Konstruktory rekurencjne *)

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

(** ** Parametry *)

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

(** ** Indukcja wzajemna *)

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

(** ** Indeksy *)

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

(** Podsumowanie (TODO) *)

(** W tym rozdziale poznaliśmy:
    - indukcję-indukcję, dzięki której możemy jednocześnie zdefiniować
      typ oraz indeksowaną nim rodzinę typów
    - indukcję-rekursję, dzięki której możemy jednoczesnie zdefiniować
      typ oraz funkcję operującą na tym typie
    - TODO *)

(** W tym rodziale poznaliśmy też paradoks Russella/Girarda i jego związek z
    twierdzeniem Cantora, autoreferencją oraz ideą uniwersum zdefiniowanego za
    pomocą indukcji-rekursji. *)