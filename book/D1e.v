(** * D1e: Rodziny typów induktywnych *)

From Typonomikon Require Import D1d.

(** * Indeksowane rodziny typów (TODO) *)

(** Słowo kluczowe [Inductive] pozwala nam definiować nie tylko typy
    induktywne, ale także rodziny typów induktywnych — i to nawet na
    dwa sposoby. W tym podrozdziale przyjrzymy się obu z nich oraz
    różnicom między nimi, a także ich wadom i zaletom. Przyjrzyjmy się
    raz jeszcze typowi [option]: *)

Print option.
(* ===> Inductive option (A : Type) : Type :=
        | Some : A -> option A
        | None : option A *)

Check Some.
(* ===> Some : forall A : Type, A -> option A *)

Check @None.
(* ===> @None : forall A : Type, option A *)

(** Definiując rodzinę typów [option], umieściliśmy argument będący typem
    w nawiasach okrągłych tuż po nazwie definiowanego typu, a przed [: Type].
    Definiując konstruktory, nie napisaliśmy nigdzie [forall A : Type, ...],
    a mimo tego komenda [Check] jasno pokazuje, że typy obydwu konstruktorów
    zaczynają się od takiej właśnie kwantyfikacji.

    (Przypomnijmy, że w przypadku [None] argument [A] jest domyślny, więc
    wyświetlenie pełnego typu tego konstruktora wymagało użycia symbolu [@],
    który oznacza "wyświetl wszystkie argumenty domyślne").

    W ogólności, definiowanie rodziny typów [T] jako [T (x1 : A1) ... (xN : AN)]
    ma następujący efekt:
    - kwantyfikacja [forall (x1 : A1) ... (xN : AN)] jest dodawana na
      początek każdego konstruktora
    - w konkluzji konstruktora [T] musi wystąpić zaaplikowany do tych
      argumentów, czyli jako [T x1 ... xN] — wstawienie innych argumentów
      jest błędem *)

Fail Inductive option' (A : Type) : Type :=
| Some' : A -> option' A
| None' : forall B : Type, option' B.

(** Próba zdefiniowania typu [option'] kończy się następującym komunikatem
    o błędzie: *)

(* Error: Last occurrence of "option'" must have "A" as 1st argument in 
   "forall B : Type, option' B". *)

(** Drugi sposób zdefiniowania rodziny typów [option] przedstawiono
    poniżej. Tym razem zamiast umieszczać argument [A : Type] po
    nazwie definiowanego typu, deklarujemy, że typem [option'] jest
    [Type -> Type]. *)

Inductive option' : Type -> Type :=
| Some' : forall A : Type, A -> option' A
| None' : forall B : Type, option' B.

(** Taki zabieg daje nam większą swobodę: w każdym konstruktorze
    z osobna musimy explicité umieścić kwantyfikację po argumencie
    sortu [Type], dzięki czemu różne konstruktory mogą w konkluzji
    mieć [option'] zaaplikowany do różnych argumentów. *)

Check Some'.
(* ===> Some' : forall A : Type, A -> option' A *)

Check None'.
(* ===> None' : forall B : Type, option' B *)

(** Zauważmy jednak, że definicje [option] i [option'] są równoważne
    — typ konstruktora [None'] różni się od typu [None] jedynie nazwą
    argumentu ([A] dla [None], [B] dla [None']).

    Jak zatem rozstrzygnąć, który sposób definiowania jest "lepszy"?
    W naszym przypadku lepszy jest sposób pierwszy, odpowiadający
    typowi [option], gdyż jest bardziej zwięzły. Nie jest to jednak
    jedyne kryterium. *)

Check option_ind.
(* ===> option_ind :
            forall (A : Type) (P : option A -> Prop),
            (forall a : A, P (Some a)) -> P None ->
            forall o : option A, P o *)

Check option'_ind.
(* ===> option'_ind :
            forall P : forall T : Type, option' T -> Prop,
            (forall (A : Type) (a : A), P A (Some' A a)) ->
            (forall B : Type, P B (None' B)) ->
            forall (T : Type) (o : option' T), P T o *)

(** Dwa powyższe termy to reguły indukcyjne, wygenerowane automatycznie
    przez Coqa dla typów [option] oraz [option']. Reguła dla [option]
    jest wizualnie krótsza, co, jak dowiemy się w przyszłości, oznacza
    zapewne, że jest prostsza, zaś prostsza reguła indukcyjna oznacza
    łatwiejsze dowodzenie przez indukcję. Jest to w zasadzie najmocniejszy
    argument przemawiający za pierwszym sposobem zdefiniowania [option].

    Powyższe rozważania nie oznaczają jednak, że sposób pierwszy jest
    zawsze lepszy — sposób drugi jest bardziej ogólny i istnieją rodziny
    typów, których zdefiniowanie sposobem pierwszym jest niemożliwe.
    Klasycznym przykładem jest rodzina typów [vec]. *)

Inductive vec (A : Type) : nat -> Type :=
| vnil : vec A 0
| vcons : forall n : nat, A -> vec A n -> vec A (S n).

(** Konstruktor [vnil] reprezentuje listę pustą, której długość wynosi
    rzecz jasna [0], zaś [vcons] reprezentuje listę składająca się z
    głowy i ogona o długości [n], której długość wynosi oczywiście [S n].

    [vec] reprezetuje listy o długości znanej statycznie (tzn. Coq zna
    długość takiej listy już w trakcie sprawdzania typów), dzięki czemu
    możemy obliczać ich długość w czasie stałym (po prostu odczytując ją
    z typu danej listy).

    Zauważ, że w obu konstruktorach argumenty typu [nat] są różne, a zatem
    zdefiniowanie tego typu jako [vec (A : Type) (n : nat) ...] byłoby
    niemożliwe.

    Przykład ten pokazuje nam również, że przy definiowaniu rodzin typów
    możemy dowolnie mieszać sposoby pierwszy i drugi — w naszym przypadku
    argument [A : Type] jest wspólny dla wszystkich konstruktorów, więc
    umieszczamy go przed ostatnim [:], zaś argument typu [nat] różni się
    w zależności od konstruktora, a zatem umieszczamy go po ostatnim [:]. *)

(** **** Ćwiczenie *)

(** Zdefiniuj następujące typy (zadbaj o to, żeby wygenerowana reguła
    indukcyjna była jak najkrótsza):
    - typ drzew binarnych przechowujących elementy typu [A]
    - typ drzew binarnych przechowujących elementy typu [A],
      których wysokość jest znana statycznie
    - typ heterogenicznych drzew binarnych (mogą one
      przechowywać elementy różnych typów)
    - typ heterogenicznych drzew binarnych, których wysokość
      jest znana statycznie *)

(* begin hide *)
Inductive BTree (A : Type) : Type :=
| BT_Empty : BTree A
| BT_Node : A -> BTree A -> BTree A -> BTree A.

Inductive EBTree (A : Type) : nat -> Type :=
| EBT_Empty : EBTree A 0
| EBT_Node :
    forall n m : nat,
      A -> EBTree A n -> EBTree A m -> EBTree A (max n m).

Inductive HBTree : Type :=
| HBT_Empty : HBTree
| HBT_Node : forall A : Type, A -> HBTree -> HBTree -> HBTree.

Check HBT_Node _ 42 (HBT_Node _ true HBT_Empty HBT_Empty) HBT_Empty.

Inductive EHBTree : nat -> Type :=
| EHBT_Empty : EHBTree 0
| EHBT_Node :
    forall (A : Type) (n m : nat),
      A -> EHBTree n -> EHBTree m -> EHBTree (max n m).
(* end hide *)

(** ** Indukcja wzajemna a indeksowane rodziny typów *)

Module MutualIndution_vs_InductiveFamilies.

(** Indukcja wzajemna nie jest zbyt użyteczna. Pierwszym, praktycznym,
    powodem jest to, że, jak pewnie zdążyłeś się już na własnej skórze
    przekonać, jej używanie jest dość upierdliwe. Drugi, teoretyczny,
    powód jest taki, że definicje przez indukcję wzajemną możemy łatwo
    zasymulować za pomocą indeksowanych rodzin typów. *)

Inductive even : nat -> Prop :=
| even0 : even 0
| evenS : forall n : nat, odd n -> even (S n)

with odd : nat -> Prop :=
| oddS : forall n : nat, even n -> odd (S n).

(** Rzućmy jeszcze raz okiem na znaną nam już definicję predykatów [even]
    i [odd] przez indukcję wzajemną. Nie dzieje się tu nic niezwykłego, a
    najważniejszym spostrzeżeniem, jakie możemy poczynić, jest to, że
    [even] i [odd] to dwa byty - nie trzy, nie pięć, ale dwa. *)

Inductive even_odd : bool -> nat -> Prop :=
| even0' : even_odd true 0
| evenS' : forall n : nat, even_odd false n -> even_odd true (S n)
| oddS'  : forall n : nat, even_odd true n -> even_odd false (S n).

Definition even' := even_odd true.
Definition odd' := even_odd false.

(** Co z tego wynika? Ano, zamiast definiować przez indukcję wzajemną dwóch
    predykatów [even] i [odd] możemy za jednym zamachem zdefiniować relację
    [even_odd], która jednocześnie odpowiada obu tym predykatom. Kluczem
    w tej sztuczce jest dodatkowy indeks, którym jest dwuelementowy typ
    [bool]. Dzięki niemu możemy zakodować definicję [even] za pomocą
    [even_odd true], zaś [odd] jako [even_odd false]. *)

Lemma even_even' :
  forall n : nat, even n -> even' n

with odd_odd' :
  forall n : nat, odd n -> odd' n.
(* begin hide *)
Proof.
  destruct n as [| n']; intro.
    constructor.
    constructor. apply odd_odd'. inversion H; assumption.
  destruct n as [| n']; intro.
    inversion H.
    constructor. apply even_even'. inversion H; assumption.
Qed.
(* end hide *)

Lemma even'_even :
  forall n : nat, even' n -> even n

with odd'_odd :
  forall n : nat, odd' n -> odd n.
(* begin hide *)
Proof.
  destruct n as [| n']; intro.
    constructor.
    constructor. apply odd'_odd. inversion H; assumption.
  destruct n as [| n']; intro.
    inversion H.
    constructor. apply even'_even. inversion H; assumption.
Qed.
(* end hide *)

(** Obie definicje są, jak widać (ćwiczenie!), równoważne, choć pod względem
    estetycznym oczywiście dużo lepiej wypada indukcja wzajemna. *)

End MutualIndution_vs_InductiveFamilies.

(** Na koniec wypada jeszcze powiedzieć, że indeksowane typy induktywne są
    potężniejsze od typów wzajemnie induktywnych. Wynika to z tego prostego
    faktu, że przez wzajemną indukcję możemy zdefiniować na raz jedynie
    skończenie wiele typów, zaś indeksowane typy induktywne mogą być
    indeksowane także typami nieskończonymi. *)

(** * Podsumowanie (TODO) *)

(** To już koniec naszej przydługiej podróży przez mechanizmy definiowania
    typów przez indukcję. W jej trakcie nauczyliśmy się bardzo wielu rzeczy.

    Zaczęliśmy od definiowania prostych enumeracji, operujących na nich
    funkcji definiowanych za pomocą dopasowania do wzorca oraz omówienia
    mechanizmu obliczania wyniku funkcji.

    Następnie poznaliśmy różne rozszerzenia tego podstawowego pomysłu
    definiowania typu za pomocą konstruktorów reprezentujących możliwe
    wartości:
    - rekurencję, dzięki której możemy definiować typy, których
      termy mają najprzeróżniejsze drzewiaste kształty
    - parametryzowane typy induktywne, których głównym zastosowaniem
      jest definiowanie kontenerów o takich samych kształtach, ale
      różnych przechowywanych typach
    - indukcję wzajemną, w praktyce niezbyt użyteczną, dzięki której
      możemy na raz zdefiniować wiele typów odnoszących się do siebie
      nawzajem
    - indeksowane rodziny typów induktywnych, dzięki którym możemy
      przez indukcję definiować predykaty oraz relacje *)

(** Nauczyliśmy się definiować funkcje przez rekursję oraz dowodzić ich
    właściwości przez indukcję. Poznaliśmy definicje poznanych w pierwszym
    rozdziale spójników logicznych oraz odpowiadających im konstrukcji na
    typach, a także definicję bardzo ważnej rodziny typów, czyli równości.

    Poznaliśmy podstawowe obiekty, którymi musi potrafić posługiwać
    się każdy programista, informatyk czy matematyk, a mianowicie
    wartości boolowskie, liczby naturalne oraz listy.

    Nauczyliśmy się formułować i implementować reguły indukcyjne (TODO:
    opisać to w głównym tekście, a nie dopiero w przypomnieniu), a także,
    co powiązane, programować listy przy pomocy foldów i unfoldów.

    Całkiem sporo, prawda? Nie? No to w kolejnych rozdziałach będzie jeszcze
    wincyj. *)