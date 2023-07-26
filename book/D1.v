(** * D1: Indukcja i rekursja *)

(** * Konstruktory rekurencyjne *)

(** Powiedzieliśmy, że termy typów induktywnych są drzewami. W przypadku
    enumeracji jest to słabo widoczne, gdyż drzewa te są zdegenerowane —
    są to po prostu punkciki oznaczone nazwami konstruktorów. Efekt
    rozgałęzienia możemy uzyskać, gdy jeden z konstruktorów będzie
    rekurencyjny, tzn. gdy jako argument będzie przyjmował term typu,
    który właśnie definiujemy. Naszym przykładem będą liczby naturalne
    (choć i tutaj rozgałęzienie będzie nieco zdegenerowane — każdy term
    będzie mógł mieć co najwyżej jedno). *)

Module NatDef.

(** Mechanizm modułów jest podobny do mechanizmu sekcji i na razie nie
    będzie nas interesował — użyjemy go, żeby nie zaśmiecać głównej
    przestrzeni nazw (mechanizm sekcji w tym przypadku by nie pomógł). *)

Inductive nat : Set :=
| O : nat
| S : nat -> nat.

Notation "0" := O.

(** Uwaga: nazwa pierwszego konstruktora to duża litera O, a nie cyfra 0
    — cyfry nie mogą być nazwami. Żeby obejść tę niedogodność, musimy
    posłużyć się mechanizmem notacji — dzięki temu będziemy mogli pisać
    0 zamiast O.

    Definicję tę możemy odczytać w następujący sposób: "[0] jest liczbą
    naturalną; jeżeli [n] jest liczbą naturalną, to [S n] również jest
    liczbą naturalną". Konstruktor [S] odpowiada tutaj dodawaniu jedynki:
    [S 0] to 1, [S (S 0)] to 2, [S (S (S 0))] to 3 i tak dalej. *)

Check (S (S (S 0))).
(* ===> S (S (S 0)) : nat *)

End NatDef.

Check S (S (S 0)).
(* ===> 3 : nat *)

(** Ręczne liczenie ilości [S] w każdej liczbie szybko staje się trudne
    nawet dla małych liczb. Na szczęście standardowa biblioteka Coqa
    udostępnia notacje, które pozwalają nam zapisywać liczby naturalne
    przy pomocy dobrze znanych nam cyfr arabskich. Żeby uzyskać do nich
    dostęp, musimy opuścić zdefiniowany przez nas moduł [NatDef], żeby
    nasza definicja [nat] nie przysłaniała tej bibliotecznej. Zaczniemy
    za to nowy moduł, żebyśmy mogli swobodnie zredefiniować działania
    na liczbach naturalnych z biblioteki standardowej. *)

Module NatOps.

Fixpoint plus (n m : nat) : nat :=
match n with
| 0 => m
| S n' => S (plus n' m)
end.

(* begin hide *)
(*Notation "n + m" := (plus n m). Dzięki notacjom będziemy też mogli pisać
    [n + m] zamiast [plus n m].*)
(* end hide *)

(** W zapisie unarnym liczby naturalne możemy wyobrażać sobie jako kupki
    [S]-ów, więc dodawanie dwóch liczb sprowadza się do przerzucenia [S]-ów
    z jednej kupki na drugą.

    Definiowanie funkcji dla typów z konstruktorami rekurencyjnymi
    wygląda podobnie jak dla enumeracji, ale występują drobne różnice:
    jeżeli będziemy używać rekurencji, musimy zaznaczyć to za pomocą
    słowa kluczowego [Fixpoint] (zamiast wcześniejszego [Definition]).
    Zauważmy też, że jeżeli funkcja ma wiele argumentów tego samego typu,
    możemy napisać [(arg1 ... argN : type)] zamiast dłuższego [(arg1 : type)
    ... (argN : type)].

    Jeżeli konstruktor typu induktywnego bierze jakieś argumenty, to wzorce,
    które go dopasowują, stają się nieco bardziej skomplikowane: poza nazwą
    konstruktora muszą też dopasowywać argumenty — w naszym przypadku używamy
    zmiennej o nazwie [n'], która istnieje tylko lokalnie (tylko we wzorcu
    dopasowania oraz po prawej stronie strzałki [=>]).

    Naszą funkcję zdefiniowaliśmy przy pomocy najbardziej elementarnego
    rodzaju rekursji, jaki jest dostępny w Coqu: rekursji strukturalnej.
    W przypadku takiej rekursji wywołania rekurencyjne mogą odbywać się
    jedynie na termach strukturalnie mniejszych, niż obecny argument
    główny rekurencji. W naszym przypadku argumentem głównym jest [n]
    (bo on jest dopasowywany), zaś rekurencyjnych wywołań dokonujemy na
    [n'], gdzie [n = S n']. [n'] jest strukturalnie mniejszy od [S n'],
    gdyż składa się z jednego [S] mniej. Jeżeli wyobrazimy sobie nasze
    liczby jako kupki [S]-ów, to wywołania rekurencyjne możemy robić
    jedynie po zdjęciu z kupki co najmniej jednego [S]. *)

(** **** Ćwiczenie (rekursja niestrukturalna) *)

(** Wymyśl funkcję z liczb naturalnych w liczby naturalne,
    która jest rekurencyjna, ale nie jest strukturalnie rekurencyjna.
    Precyzyjniej pisząc: później okaże się, że wszystkie formy
    rekurencji to tak naprawdę rekursja strukturalna pod przykrywką.
    Wymyśl taką definicję, która na pierwszy rzut oka nie jest
    strukturalnie rekurencyjna. *)

(* begin hide *)
(** Odpowiedź: dzielenie. *)
(* end hide *)

(** Podobnie jak w przypadku funkcji [negb], tak i tym razem w celu
    sprawdzenia poprawności naszej definicji spróbujemy udowodnić, że
    posiada ona właściwości, których się spodziewamy. *)

Lemma plus_O_n :
  forall n : nat, plus 0 n = n.
Proof.
  intro. cbn. trivial.
Qed.

(** Tak prosty dowód nie powinien nas dziwić — wszakże twierdzenie to
    wynika wprost z definicji (spróbuj zredukować "ręcznie" wyrażenie
    [0 + n]). *)

Lemma plus_n_O_try1 :
  forall n : nat, plus n 0 = n.
Proof.
  intro. destruct n.
    trivial.
    cbn. f_equal.
Abort.

(** Tym razem nie jest już tak prosto — [n + 0 = n] nie wynika z definicji
    przez prostą redukcję, gdyż argumentem głównym funkcji [plus] jest
    jej pierwszy argument, czyli [n]. Żeby móc zredukować to wyrażenie,
    musimy rozbić [n]. Pokazanie, że [0 + 0 = 0] jest trywialne, ale
    drugi przypadek jest już beznadziejny. Ponieważ funkcje zachowują
    równość (czyli [a = b] implikuje [f a = f b]), to aby pokazać, że
    [f a = f b], wystarczyć pokazać, że [a = b] — w ten właśnie sposób
    działa taktyka [f_equal]. Nie pomogła nam ona jednak — po jej
    użyciu mamy do pokazania to samo, co na początku, czyli [n + 0 = n]. *)

Lemma plus_n_O :
  forall n : nat, plus n 0 = n.
Proof.
  intro. induction n.
    trivial.
    cbn. f_equal. assumption.
Qed.

(** Do udowodnienia tego twierdzenia musimy posłużyć się indukcją.
    Indukcja jest sposobem dowodzenia właściwości typów induktywnych
    i funkcji rekurencyjnych, który działa mniej więcej tak: żeby
    udowodnić, że każdy term typu [A] posiada własność [P], pokazujemy
    najpierw, że konstruktory nierekurencyjne posiadają tę własność
    dla dowolnych argumentów, a następnie, że konstruktory rekurencyjne
    zachowują tę własność.

    W przypadku liczb naturalnych indukcja wygląda tak: żeby pokazać,
    że każda liczba naturalna ma własność [P], najpierw należy
    pokazać, że zachodzi [P 0], a następnie, że jeżeli zachodzi [P n],
    to zachodzi także [P (S n)]. Z tych dwóch reguł możemy zbudować
    dowód na to, że [P n] zachodzi dla dowolnego [n].

    Ten sposób rozumowania możemy zrealizować w Coqu przy pomocy
    taktyki [induction]. Działa ona podobnie do [destruct], czyli
    rozbija podany term na konstruktory, ale w przypadku konstruktorów
    rekurencyjnych robi coś jeszcze — daje nam założenie indukcyjne,
    które mówi, że dowodzone przez nas twierdzenie zachodzi dla
    rekurencyjnych argumentów konstruktora. Właśnie tego było nam
    trzeba: założenie indukcyjne pozwala nam dokończyć dowód. *)

Lemma add_comm :
  forall n m : nat, plus n m = plus m n.
Proof.
  induction n as [| n']; cbn; intros.
    rewrite plus_n_O. trivial.
    induction m as [| m'].
      cbn. rewrite plus_n_O. trivial.
      cbn. rewrite IHn'. rewrite <- IHm'. cbn. rewrite IHn'.
        trivial.
Qed.

(** Pojedyncza indukcja nie zawsze wystarcza, co obrazuje powyższy przypadek.
    Zauważmy, że przed użyciem [induction] nie musimy wprowadzać zmiennych
    do kontekstu — taktyka ta robi to sama, podobnie jak [destruct].
    Również podobnie jak [destruct], możemy przekazać jej wzorzec, którym
    nadajemy nazwy argumentom konstruktorów, na które rozbijany jest term.
    
    W ogólności wzorzec ma postać [[a11 .. a1n | ... | am1 .. amk]]. Pionowa
    kreska oddziela argumenty poszczególnych konstruktorów: [a11 .. a1n]
    to argumenty pierwszego konstruktora, zaś [am1 .. amk] to argumenty
    m-tego konstruktora. [nat] ma dwa konstruktory, z czego pierwszy nie
    bierze argumentów, a drugi bierze jeden, więc nasz wzorzec ma postać
    [[| n']]. Dzięki temu nie musimy polegać na domyślnych nazwach nadawanych
    argumentom przez Coqa, które często wprowadzają zamęt.

    Jeżeli damy taktyce [rewrite] nazwę hipotezy lub twierdzenia, którego
    konkluzją jest [a = b], to zamienia ona w obecnym podcelu wszystkie
    wystąpienia [a] na [b] oraz generuje tyle podcelów, ile przesłanek ma
    użyta hipoteza lub twierdzenie. W naszym przypadku użyliśmy udowodnionego
    uprzednio twierdzenia [plus_n_O], które nie ma przesłanek, czego efektem
    było po prostu przepisanie [plus m 0] na [m].

    Przepisywać możemy też w drugą stronę pisząc [rewrite <-]. Wtedy jeżeli
    konkluzją danego twierdzenia lub hipotezy jest [a = b], to w celu wszystkie
    [b] zostaną zastąpione przez [a]. *)

(** **** Ćwiczenie (mnożenie) *)

(** Zdefiniuj mnożenie i udowodnij jego właściwości. *)

(* begin hide *)
Fixpoint mult (n m : nat) : nat :=
match n with
| 0 => 0
| S n' => plus m (mult n' m)
end.
(* end hide *)

Lemma mult_0_l :
  forall n : nat, mult 0 n = 0.
(* begin hide *)
Proof.
  induction n; trivial.
Qed.
(* end hide *)

Lemma mult_0_r :
  forall n : nat, mult n 0 = 0.
(* begin hide *)
Proof.
  induction n as [| n'].
    cbn. trivial.
    cbn. assumption.
Restart.
  induction n; trivial.
Qed.
(* end hide *)

Lemma mult_1_l :
  forall n : nat, mult 1 n = n.
(* begin hide *)
Proof.
  destruct n as [| n'].
    cbn. trivial.
    cbn. rewrite plus_n_O. trivial.
Restart.
  destruct n; cbn; try rewrite plus_n_O; trivial.
Qed.
(* end hide*)

Lemma mult_1_r :
  forall n : nat, mult n 1 = n.
(* begin hide *)
Proof.
  induction n.
    cbn. trivial.
    cbn. rewrite IHn. trivial.
Restart.
  induction n; cbn; try rewrite IHn; trivial.
Qed.
(* end hide *)

(** Jeżeli ćwiczenie było za proste i czytałeś podrozdział o kombinatorach
    taktyk, to spróbuj udowodnić:
    - dwa pierwsze twierdzenia używając nie więcej niż 2 taktyk
    - trzecie bez użycia indukcji, używając nie więcej niż 4 taktyk
    - czwarte używając nie więcej niż 4 taktyk *)

(** Wszystkie dowody powinny być nie dłuższe niż pół linijki. *)

(** **** Ćwiczenie (inne dodawanie) *)

(** Dodawanie można alternatywnie zdefiniować także w sposób przedstawiony
    poniżej. Udowodnij, że ta definicja jest równoważna poprzedniej. *)

Fixpoint plus' (n m : nat) : nat :=
match m with
| 0 => n
| S m' => plus' (S n) m'
end.

Lemma plus'_n_0 :
  forall n : nat, plus' n 0 = n.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma plus'_S :
  forall n m : nat, plus' (S n) m = S (plus' n m).
(* begin hide *)
Proof.
  intros. generalize dependent n.
  induction m as [| m']; cbn; intros.
    reflexivity.
    rewrite IHm'. reflexivity.
Qed.
(* end hide *)

Lemma plus'_0_n :
  forall n : nat, plus' 0 n = n.
(* begin hide *)
Proof.
  induction n as [| n'].
    trivial.
    cbn. rewrite plus'_S. rewrite IHn'. trivial.
Qed.
(* end hide *)

Lemma plus'_comm :
  forall n m : nat, plus' n m = plus' m n.
(* begin hide *)
Proof.
  intros. generalize dependent n. induction m as [| m']; cbn; intros.
    rewrite plus'_0_n. trivial.
    rewrite IHm'. cbn. trivial.
Qed.
(* end hide *)

Lemma plus'_is_plus :
  forall n m : nat, plus' n m = plus n m.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intro.
    apply plus'_0_n.
    rewrite <- IHn'. rewrite plus'_S. trivial.
Qed.
(* end hide *)

End NatOps.

(** ** Reguły indukcji *)

Module rec.

Unset Elimination Schemes.

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

(** * Listy, czyli parametry + rekursja *)

(** Połączenie funkcji zależnych, konstruktorów rekurencyjnych i
    polimorfizmu pozwala nam na opisywanie (prawie) dowolnych typów.
    Jednym z najbardziej podstawowych i najbardziej przydatnych
    narzędzi w programowaniu funkcyjnym (i w ogóle w życiu) są listy. *)

Module MyList.

Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.

(** Lista przechowuje wartości pewnego ustalonego typu [A] (a więc nie
    można np. trzymać w jednej liście jednocześnie wartości typu [bool] i
    [nat]) i może mieć jedną z dwóch postaci: może być pusta (konstruktor
    [nil]) albo składać się z głowy i ogona (konstruktor [cons]). Głowa
    listy to wartość typu [A], zaś jej ogon to inna lista przechowująca
    wartości typu [A]. *)

Check nil.
(* ===> nil : forall A : Type, list A *)

Check cons.
(* ===> cons : forall A : Type, A -> list A -> list A *)

Arguments nil  {A}.
Arguments cons {A} _ _.

(** Jak już wspomnieliśmy, jeżeli typ induktywny ma argument (w naszym
    przypadku [A : Type]), to argument ten jest też pierwszym argumentem
    każdego z konstruktorów. W przypadku konstruktora [cons] podawanie
    argumentu [A] jest zbędne, gdyż kolejnym jego argumentem jest wartość
    tego typu. Wobec tego Coq może sam go wywnioskować, jeżeli mu każemy.

    Robimy to za pomocą komendy [Arguments konstruktor argumenty].
    Argumenty w nawiasach kwadratowych Coq będzie traktował jako domyślne,
    a te oznaczone podkreślnikiem trzeba będzie zawsze podawać ręcznie.
    Nazwa argumentu domyślnego musi być taka sama jak w definicji typu
    (w naszym przypadku w definicji [list] argument nazywał się [A],
    więc tak też musimy go nazwać używając komendy [Arguments]). Musimy
    wypisać wszystkie argumenty danego konstruktora — ich ilość możemy
    sprawdzić np. komendą [Check].

    Warto w tym momencie zauważyć, że Coq zna typy wszystkich termów,
    które zostały skonstruowane — gdyby tak nie było, nie mógłby
    sam uzupełniać argumentów domyślnych, a komenda [Check] nie mogłaby
    działać. *)

Notation "[]" := nil.
Infix "::" := (cons) (at level 60, right associativity ).

Check [].
(* ===> [[]] : list ?254 *)

Check 0 :: 1 :: 2 :: nil.
(* ===> [[0; 1; 2]] : list nat *)

(** Nazwy [nil] i [cons] są zdecydowanie za długie w porównaniu do swej
    częstości występowania. Dzięki powyższym eleganckim notacjom
    zaoszczędzimy sobie trochę pisania. Jeżeli jednak notacje utrudniają
    nam np. odczytanie celu, który mamy udowodnić, możemy je wyłączyć
    odznaczając w CoqIDE View > Display Notations.

    Wynik [[] : list ?254] (lub podobny) wyświetlony przez Coqa dla [[]]
    mówi nam, że [[]] jest listą pewnego ustalonego typu, ale Coq jeszcze
    nie wie, jakiego (bo ma za mało informacji, bo wywnioskować argument
    domyślny konstruktora [nil]). *)

Notation "[ x ]" := (cons x nil).
Notation "[ x ; y ; .. ; z ]" :=
    (cons x (cons y .. (cons z nil) .. )).

Check [5].
(* ===> [[5]] : list nat *)

Check [0; 1; 2; 3].
(* ===> [[0; 1; 2; 3]] : list nat *)

(** Zauważ, że system notacji Coqa jest bardzo silny — ostatnia notacja
    (ta zawierająca [..]) jest rekurencyjna. W innych językach tego typu
    notacje są zazwyczaj wbudowane w język i ograniczają się do podstawowych
    typów, takich jak listy właśnie. *)

Fixpoint app {A : Type} (l1 l2 : list A) : list A :=
match l1 with
| [] => l2
| h :: t => h :: app t l2
end.

Notation "l1 ++ l2" := (app l1 l2).

(** Funkcje na listach możemy definiować analogicznie do funkcji na
    liczbach naturalnych. Zaczniemy od słowa kluczowego [Fixpoint],
    gdyż będziemy potrzebować rekurencji. Pierwszym argumentem naszej
    funkcji będzie typ [A] — musimy go wymienić, bo inaczej nie będziemy
    mogli mieć argumentów typu [list A] (pamiętaj, że samo [list]
    jest rodziną typów, a nie typem). Zapis [{A : Type}] oznacza,
    że Coq ma traktować [A] jako argument domyślny — jest to szybszy
    sposób, niż użycie komendy [Arguments].

    Nasz funkcja ma za zadanie dokleić na końcu (ang. append) pierwszej
    listy drugą listę. Definicja jest dość intuicyjna: doklejenie jakiejś
    listy na koniec listy pustej daje pierwszą listę, a doklejenie listy
    na koniec listy mającej głowę i ogon jest doklejeniem jej na koniec
    ogona. *)

Eval compute in [1; 2; 3] ++ [4; 5; 6].
(* ===> [[1; 2; 3; 4; 5; 6]] : list nat *)

(** Wynik działania naszej funkcji wygląda poprawnie, ale niech cię
    nie zwiodą ładne oczka — jedynym sposobem ustalenia poprawności
    naszego kodu jest udowodnienie, że posiada on pożądane przez
    nas właściwości. *)

Lemma app_nil_l :
  forall (A : Type) (l : list A), [] ++ l = l.
Proof.
  intros. cbn. reflexivity.
Qed.

Lemma app_nil_r :
  forall (A : Type) (l : list A), l ++ [] = l.
Proof.
  induction l as [| h t].
    cbn. reflexivity.
    cbn. rewrite IHt. reflexivity.
Qed.

(** Sposoby dowodzenia są analogiczne jak w przypadku liczb naturalnych.
    Pierwsze twierdzenie zachodzi na mocy samej definicji funkcji [app]
    i dowód sprowadza się do wykonania programu za pomocą taktyki [cbn].
    Drugie jest analogiczne do twierdzenia [plus_n_0], z tą różnicą, że
    w drugim celu zamiast [f_equal] posłużyliśmy się taktyką [rewrite].

    Zauważ też, że zmianie uległa postać wzorca przekazanego taktyce
    [induction] — teraz ma on postać [[| h t]], gdyż [list] ma 2
    konstruktory, z których pierwszy, [nil], nie bierze argumentów
    (argumenty domyślne nie są wymieniane we wzorcach), zaś drugi, [cons],
    ma dwa argumenty — głowę, tutaj nazwaną [h] (jako skrót od ang. head)
    oraz ogon, tutaj nazwany [t] (jako skrót od ang. tail). *)

(** **** Ćwiczenie (właściwości funkcji [app])*)

(** Udowodnij poniższe właściwości funkcji [app]. Wskazówka: może ci się
    przydać taktyka [specialize]. *)

Lemma app_assoc :
  forall (A : Type) (l1 l2 l3 : list A),
    l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    reflexivity.
    rewrite <- IHt1. reflexivity.
Qed.
(* end hide *)

Lemma app_not_comm :
  ~ forall (A : Type) (l1 l2 : list A), l1 ++ l2 = l2 ++ l1.
(* begin hide *)
Proof.
  intro. specialize (H nat [0] [1]). cbn in H. inversion H.
Qed.
(* end hide *)

(** **** Ćwiczenie ([length]) *)

(** Zdefiniuj funkcję [length], która oblicza długość listy, a następnie
    udowodnij poprawność swojej implementacji. *)

(* begin hide *)
Fixpoint length {A : Type} (l : list A) : nat :=
match l with
| [] => 0
| h :: t => S (length t)
end.
(* end hide *)

Lemma length_nil :
  forall A : Type, length (@nil A) = 0.
(* begin hide *)
Proof.
  intro. cbn. reflexivity.
Qed.
(* end hide *)

Lemma length_cons :
  forall (A : Type) (h : A) (t : list A), length (h :: t) <> 0.
(* begin hide *)
Proof.
  cbn. intros. inversion 1.
Qed.
(* end hide *)

Lemma length_app :
  forall (A : Type) (l1 l2 : list A),
    length (l1 ++ l2) = length l1 + length l2.
(* begin hide *)
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    reflexivity.
    f_equal. rewrite IHt1. reflexivity.
Qed.
(* end hide *)

End MyList.

(** * Kiedy typ induktywny jest pusty? *)

(** Typy puste to typy, które nie mają żadnych elementów. Z jednym z nich
    już się spotkaliśmy — był to [Empty_set], który jest pusty, gdyż nie
    ma żadnych konstruktorów. Czy wszystkie typy puste to typy, które
    nie mają konstruktorów? *)

Inductive Empty : Type :=
| c : Empty_set -> Empty.

Lemma Empty_is_empty :
  forall empty : Empty, False.
Proof.
  intro. destruct empty. destruct e.
Qed.

(** Okazuje się, że nie. Pustość i niepustość jest kwestią czegoś więcej,
    niż tylko ilości konstruktorów. Powyższy przykład pokazuje dobitnie,
    że ważne są też typy argumentów konstruktorów. Jeżeli typ któregoś z
    argumentów konstruktora jest pusty, to nie można użyć go do zrobienia
    żadnego termu. Jeżeli każdy konstruktor typu [T] ma argument, którego
    typ jest pusty, to sam typ [T] również jest pusty.

    Wobec powyższych rozważań możemy sformułować następujące kryterium:
    typ [T] jest niepusty, jeżeli ma co najmniej jeden konstruktor, który
    nie bierze argumentów, których typy są puste. Jakkolwiek jest to bardzo
    dobre kryterium, to jednak nie rozwiewa ono niestety wszystkich możliwych
    wątpliwości. *)

Inductive InfiniteList (A : Type) : Type :=
| InfiniteCons : A -> InfiniteList A -> InfiniteList A.

(** Czy typ [InfiniteList A] jest niepusty? Skorzystajmy z naszego kryterium:
    ma on jeden konstruktor biorący dwa argumenty, jeden typu [A] oraz drugi
    typu [InfiniteList A]. W zależności od tego, czym jest [A], może on być
    pusty lub nie — przyjmijmy, że [A] jest niepusty. W przypadku drugiego
    argumentu napotykamy jednak na problem: to, czy [InfiniteList A] jest
    niepusty zależy od tego, czy typ argumentu jego konstruktora, również
    [InfiniteList A], jest niepusty. Sytuacja jest więc beznadziejna — mamy
    błędne koło.

    Powyższy przykład pokazuje, że nasze kryterium może nie poradzić sobie
    z rekurencją. Jak zatem rozstrzygnąć, czy typ ten jest niepusty? Musimy
    odwołać się bezpośrednio do definicji i zastanowić się, czy możliwe jest
    skonstruowanie jakichś jego termów. W tym celu przypomnijmy, czym są typy
    induktywne:
    - Typ induktywny to rodzaj planu, który pokazuje, w jaki sposób można
      konstruować jego termy, które są drzewami.
    - Konstruktory to węzły drzewa. Ich nazwy oraz ilość i typy argumentów
      nadają drzewu kształt i znaczenie.
    - Konstruktory nierekurencyjne to liście drzewa.
    - Konstruktory rekurencyjne to węzły wewnętrzne drzewa. *)

(** Kluczowym faktem jest rozmiar termów: o ile rozgałęzienia mogą być
    potencjalnie nieskończone, o tyle wszystkie gałęzie muszą mieć
    skończoną długość. Pociąga to za sobą bardzo istotny fakt: typy
    mające jedynie konstruktory rekurencyjne są puste, gdyż bez użycia
    konstruktorów nierekurencyjnych możemy konstruować jedynie drzewa
    nieskończone (i to tylko przy nierealnym założeniu, że możliwe jest
    zakończenie konstrukcji liczącej sobie nieskończoność kroków). *)

Lemma InfiniteList_is_empty :
  forall A : Type, InfiniteList A -> False.
Proof.
  intros A l. induction l as [h t]. exact IHt.
Qed.

(** Pokazanie, że [InfiniteList A] jest pusty, jest bardzo proste —
    wystarczy posłużyć się indukcją. Indukcja po [l : InfiniteList A]
    daje nam hipotezę indukcyjną [IHt : False], której możemy użyć,
    aby natychmiast zakończyć dowód.

    Zaraz, co właściwie się stało? Dlaczego dostaliśmy zupełnie za darmo
    hipotezę [IHt], która jest szukanym przez nas dowodem? W ten właśnie
    sposób przeprowadza się dowody indukcyjne: zakładamy, że hipoteza [P]
    zachodzi dla termu [t : InfiniteList A], a następnie musimy pokazać,
    że [P] zachodzi także dla termu [InfiniteCons h t]. Zazwyczaj [P] jest
    predykatem i wykonanie kroku indukcyjnego jest nietrywialne, w naszym
    przypadku jest jednak inaczej — postać [P] jest taka sama dla [t] oraz
    dla [InfiniteCons h t] i jest nią [False].

    Czy ten konfundujący fakt nie oznacza jednak, że [list A], czyli typ
    zwykłych list, również jest pusty? Spróbujmy pokazać, że tak jest. *)

Lemma list_empty :
  forall (A : Type), list A -> False.
Proof.
  intros A l. induction l as [| h t].
    2: { exact IHt. }
Abort.

(** Pokazanie, że typ [list A] jest pusty, jest rzecz jasna niemożliwe,
    gdyż typ ten zdecydowanie pusty nie jest — w jego definicji stoi
    jak byk napisane, że dla dowolnego typu [A] istnieje lista termów
    typu [A]. Jest nią oczywiście [@nil A].

    Przyjrzyjmy się naszej próbie dowodu. Próbujemy posłużyć się indukcją
    w ten sam sposób co poprzednio. Taktyka [induction] generuje nam dwa
    podcele, gdyż [list] ma dwa konstruktory — pierwszy podcel dla [nil],
    a drugi dla [cons]. Komenda [n: { ... }] pozwala nam przełączyć się do
    n-tego celu (w naszym przypadku celu nr 2, czyli gdy [l] jest postaci
    [cons h t]). Uwaga: przestarzałym sposobem na przełączanie celów jest
    komenda [Focus] - jeżeli zobaczysz gdzieś jej użycie, to znaczy, że po
    prostu zapomniałem tego poprawić.

    Sprawa wygląda identycznie jak poprzednio — za darmo dostajemy hipotezę
    [IHt : False], której używamy do natychmiastowego rozwiązania naszego
    celu. Tym, co stanowi przeszkodę nie do pokonania, jest cel nr 1, czyli
    gdy [l] zrobiono za pomocą konstruktora [nil]. Ten konstruktor nie jest
    rekurencyjny, więc nie dostajemy żadnej hipotezy indukcyjnej. Lista [l]
    zostaje w każdym miejscu, w którym występuje, zastąpiona przez [[]], a
    ponieważ nie występuje nigdzie — znika. Musimy teraz udowodnić fałsz
    wiedząc jedynie, że [A] jest typem, co jest niemożliwe. *)

(** * Induktywne predykaty i relacje *)

(** Przypomnijmy, że predykaty to funkcje, których przeciwdziedziną jest
    sort [Prop], czyli funkcje zwracające zdania logiczne. Predykat
    [P : A -> Prop] można rozumieć jako właściwość, którą mogą posiadać
    termy typu [A], zaś dla konkretnego [x : A] zapis [P x] interpretować
    można "term [x] posiada właściwóść [P]".

    O ile istnieją tylko dwa rodzaje induktwynych zdań (prawdziwe i fałszywe),
    o tyle induktywnie zdefiniowane predykaty są dużo bardziej ciekawe i
    użyteczne, gdyż dla jednych termów mogą być prawdziwe, a dla innych nie. *)

Inductive even : nat -> Prop :=
| even0 : even 0
| evenSS : forall n : nat, even n -> even (S (S n)).

(** Predykat [even] ma oznaczać właściwość "bycia liczbą parzystą". Jego
    definicję można zinterpretować tak:
    - "[0] jest liczbą przystą"
    - "jeżeli [n] jest liczbą parzystą, to [n + 2] również jest
       liczbą parzystą" *)

(** Jak widać, induktywna definicja parzystości różni się od powszechnie
    używanej definicji, która głosi, że "liczba jest parzysta, gdy
    dzieli się bez reszty przez 2". Różnica jest natury filozoficznej:
    definicja induktywna mówi, jak konstruować liczby parzyste, podczas
    gdy druga, "klasyczna" definicja mówi, jak sprawdzić, czy liczba
    jest parzysta.

    Przez wzgląd na swą konstruktywność, w Coqu induktywne definicje
    predykatów czy relacji są często dużo bardziej użyteczne od tych
    nieinduktywnych, choć nie wszystko można zdefiniować induktywnie. *)

Lemma zero_is_even : even 0.
Proof.
  apply even0.
Qed.

(** Jak możemy udowodnić, że [0] jest liczbą parzystą? Posłuży nam
    do tego konstruktor [even0], który wprost głosi, że [even 0].
    Nie daj się zwieść: [even0], pisane bez spacji, jest nazwą
    konstruktora, podczas gdy [even 0], ze spacją, jest zdaniem
    (czyli termem typu [Prop]), które można interpretować jako
    "[0] jest liczbą parzystą". *)

Lemma two_is_even : even 2.
Proof.
  apply evenSS. apply even0.
Qed.

(** Jak możemy udowodnić, że [2] jest parzyste? Konstruktor [even0]
    nam nie pomoże, gdyż jego postać ([even 0]) nie pasuje do postaci
    naszego twierdzenia ([even 2]). Pozostaje nam jednak konstruktor
    [evenSS].

    Jeżeli przypomnimy sobie, że [2] to tak naprawdę [S (S 0)],
    natychmiast dostrzeżemy, że jego konkluzja pasuje do postaci naszego
    twierdzenia. Możemy go więc zaaplikować (pamiętaj, że konstruktory są
    jak zwykłe funkcje, tylko że niczego nie obliczają — nadają one typom
    ich kształty). Teraz wystarczy pokazać, że [even 0] zachodzi, co już
    potrafimy. *)

Lemma four_is_even : even 4.
Proof.
  constructor. constructor. constructor.
Qed.

(** Jak pokazać, że [4] jest parzyste? Tą samą metodą, która pokazaliśmy,
    że [2] jest parzyste. [4] to [S (S (S (S 0)))], więc możemy użyć
    konstruktora [evenSS]. Zamiast jednak pisać [apply evenSS], możemy
    użyć taktyki [constructor]. Taktyka ta działa na celach, w których
    chcemy skonstruować wartość jakiegoś typu induktywnego (a więc także
    gdy dowodzimy twierdzeń o induktywnych predykatach). Szuka ona
    konstruktora, który może zaaplikować na celu, i jeżeli znajdzie, to
    aplikuje go, a gdy nie — zawodzi.

    W naszym przypadku pierwsze dwa użycia [constructor] aplikują
    konstruktor [evenSS], a trzecie — konstruktor [even0]. *)

Lemma the_answer_is_even : even 42.
Proof.
  repeat constructor.
Qed.

(** A co, gdy chcemy pokazać, że [42] jest parzyste? Czy musimy 22 razy
    napisać [constructor]? Na szczęście nie — wystarczy posłużyć się
    kombinatorem [repeat] (jeżeli nie pamiętasz, jak działa, zajrzyj do
    rozdziału 1). *)

Lemma one_not_even_failed : ~ even 1.
Proof.
  unfold not. intro. destruct H.
Abort.

Lemma one_not_even : ~ even 1.
Proof.
  unfold not. intro. inversion H.
Qed.

(** A jak pokazać, że [1] nie jest parzyste? Mając w kontekście dowód
    na to, że [1] jest parzyste ([H : even 1]), możemy zastantowić się,
    w jaki sposób dowód ten został zrobiony. Nie mógł zostać zrobiony
    konstruktorem [even0], gdyż ten dowodzi, że [0] jest parzyste, a
    przecież przekonaliśmy się już, że [0] to nie [1]. Nie mógł też
    zostać zrobiony konstruktorem [evenSS], gdyż ten ma w konkluzji
    [even (S (S n))], podczas gdy [1] jest postaci [S 0] — nie pasuje
    on do konkluzji [evenSS], gdyż "ma za mało [S]ów".

    Nasze rozumowanie prowadzi do wniosku, że za pomocą [even0] i [evenSS],
    które są jedynymi konstruktorami [even], nie można skonstruować [even 1],
    więc [1] nie może być parzyste. Na podstawie wcześniejszych doświadczeń
    mogłoby się nam wydawać, że [destruct] załatwi sprawę, jednak tak nie
    jest — taktyka ta jest w tym przypadku upośledzona i nie potrafi nam
    pomóc. Zamiast tego możemy się posłużyć taktyką [inversion]. Działa ona
    dokładnie w sposób opisany w poprzednim akapicie. *)

Lemma three_not_even : ~ even 3.
Proof.
  intro. inversion H. inversion H1.
Qed.

(** Jak pokazać, że [3] nie jest parzyste? Pomoże nam w tym, jak poprzednio,
    inwersja. Tym razem jednak nie załatwia ona sprawy od razu. Jeżeli
    zastanowimy się, jak można pokazać [even 3], to dojdziemy do wniosku,
    że można to zrobić konstruktorem [evenSS], gdyż [3] to tak naprawdę
    [S (S 1)]. To właśnie robi pierwsza inwersja: mówi nam, że [H : even 3]
    można uzyskać z zaaplikowania [evenSS] do [1], jeżeli tylko mamy dowód
    [H1 : even 1] na to, że [1] jest parzyste. Jak pokazać, że [1] nie
    jest parzyste, już wiemy. *)

(** **** Ćwiczenie (odd) *)

(** Zdefiniuj induktywny predykat [odd], który ma oznaczać "bycie liczbą
    nieparzystą" i udowodnij, że zachowuje się on jak należy. *)

(* begin hide *)
Inductive odd : nat -> Prop :=
| odd1 : odd 1
| oddSS : forall n : nat, odd n -> odd (S (S n)).
(* end hide *)

Lemma one_odd : odd 1.
(* begin hide *)
Proof.
  constructor.
Qed.
(* end hide *)

Lemma seven_odd : odd 7.
(* begin hide *)
Proof.
  repeat constructor.
Qed.
(* end hide *)

Lemma zero_not_odd : ~ odd 0.
(* begin hide *)
Proof.
  inversion 1.
Qed.
(* end hide *)

Lemma two_not_odd : ~ odd 2.
(* begin hide *)
Proof.
  inversion 1. inversion H1.
Qed.
(* end hide *)

(** ** Indukcja po dowodzie *)

Require Import Arith.

(** Biblioteka [Arith] zawiera różne definicje i twierdzenia dotyczące
    arytmetyki. Będzie nam ona potrzebna w tym podrozdziale.

    Jak udowodnić, że suma liczb parzystych jest parzysta? Być może
    właśnie pomyślałeś o indukcji. Spróbujmy zatem: *)

Lemma even_sum_failed1 :
  forall n m : nat, even n -> even m -> even (n + m).
Proof.
  induction n as [| n']; cbn; intros.
    trivial.
    induction m as [| m']; rewrite Nat.add_comm; cbn; intros.
      assumption.
      constructor. rewrite Nat.add_comm. apply IHn'.
Abort.

(** Próbując jednak indukcji po [n], a potem po [m], docieramy do martwego
    punktu. Musimy udowodnić [even n'], podczas gdy zachodzi [even (S n')]
    (czyli [even n'] jest fałszywe). Wynika to z faktu, że przy indukcji
    [n] zwiększa się o 1 ([P n -> P (S n)]), podczas gdy w definicji
    [even] mamy konstruktor głoszący, że ([even n -> even (S (S n))]).

    Być może w drugiej kolejności pomyślałeś o taktyce [destruct]: jeżeli
    sprawdzimy, w jaki sposób udowodniono [even n], to przy okazji dowiemy
    się też, że [n] może być jedynie postaci [0] lub [S (S n')]. Dzięki
    temu powinniśmy uniknąć problemu z poprzedniej próby. *)

Lemma even_sum_failed2 :
  forall n m : nat, even n -> even m -> even (n + m).
Proof.
  intros n m Hn Hm. destruct Hn, Hm; cbn.
    constructor.
    constructor. assumption.
    rewrite Nat.add_comm. cbn. constructor. assumption.
    rewrite Nat.add_comm. cbn. do 2 constructor.
Abort.

(** Niestety, taktyka [destruct] okazała się za słaba. Predykat [even] jest
    induktywny, a zatem bez indukcji się nie obędzie. Rozwiązaniem naszych
    problemów nie będzie jednak indukcja po [n] lub [m], lecz po dowodzie na
    to, że [n] jest parzyste. *)

Lemma even_sum :
  forall n m : nat, even n -> even m -> even (n + m).
Proof.
  intros n m Hn Hm. induction Hn as [| n' Hn'].
    cbn. assumption.
    cbn. constructor. assumption.
Qed.

(** Indukcja po dowodzie działa dokładnie tak samo, jak indukcja, z którą
    zetknęliśmy się dotychczas. Różni się od niej jedynie tym, że aż do
    teraz robiliśmy indukcję jedynie po termach, których typy były sortu
    [Set] lub [Type]. Indukcja po dowodzie to indukcja po termie, którego
    typ jest sortu [Prop].

    W naszym przypadku użycie [induction Hn] ma następujący skutek:
    - W pierwszym przypadku [Hn] to po prostu konstruktor [even0], a 
      zatem [n] jest zerem.
    - W drugim przypadku [Hn] to [evenSS n' Hn'], gdzie [n] jest postaci
      [S (S n')], zaś [Hn'] jest dowodem na to, że [n'] jest parzyste. *)

(** ** Taktyki [replace] i [assert] *)

(** Przy następnych ćwiczeniach mogą przydać ci się taktyki [replace]
    oraz [assert]. *)

Lemma stupid_example_replace :
  forall n : nat, n + 0 = n.
Proof.
  intro. replace (n + 0) with (0 + n).
    trivial.
    apply Nat.add_comm.
Qed.

(** Taktyka [replace t with t'] pozwala nam zastąpić w celu każde
    wystąpienie termu [t] termem [t']. Jeżeli [t] nie ma w celu, to
    taktyka zawodzi, a w przeciwnym wypadku dodaje nam jeden podcel,
    w którym musimy udowodnić, że [t = t']. Można też zastosować ją
    w hipotezie, pisząc [replace t with t' in H]. *)

Lemma stupid_example_assert :
  forall n : nat, n + 0 + 0 = n.
Proof.
  intro. assert (H : n + 0 = n).
    apply Nat.add_0_r.
    do 2 rewrite H. trivial.
Qed.

(** Taktyka [assert (x : A)] dodaje do kontekstu term [x] typu [A] oraz
    generuje jeden dodatkowy podcel, w którym musimy skonstruować [x].
    Zawodzi ona, jeżeli nazwa [x] jest już zajęta. *)

(** **** Ćwiczenie (właściwości [even]) *)

(** Udowodnij poniższe twierdzenia. Zanim zaczniesz, zastanów się, po czym
    należy przeprowadzić indukcję: po wartości, czy po dowodzie? *)

Lemma double_is_even :
  forall n : nat, even (2 * n).
(* begin hide *)
Proof.
  induction n as [| n']; cbn in *.
    constructor.
    rewrite <- plus_n_O in *. rewrite Nat.add_comm. cbn.
      constructor. assumption.
Qed.
(* end hide *)

Lemma even_is_double :
  forall n : nat, even n -> exists k : nat, n = 2 * k.
(* begin hide *)
Proof.
  induction 1.
    exists 0. trivial.
    destruct IHeven. exists (S x). cbn in *. rewrite <- plus_n_O in *.
      rewrite Nat.add_comm. cbn. do 2 f_equal. assumption.
Qed.
(* end hide *)

(** * "Paradoksy" indukcji (TODO) *)

(** ** Paradoks sterty (TODO) *)

(** ** Wszystkie konie sa tego samego koloru (TODO) *)

(** ** Paradoks najmniejszej interesującej liczby naturalnej (TODO) *)

(** * Indukcja matematyczna a indukcja w nauce (TODO) *)

(* begin hide *)
(* TODO: Dekonfuzja: indukcja matematyczna to rozumowanie dedukcyjne, a nie indukcyjne. *)
(* end hide *)