(** * D2ef: Typy zagnieżdżone [TODO] *)

Require Import List.
Import ListNotations.

From Typonomikon Require Import D2c.

(** TODO: moje RoseTree jest ujowe *)

(** Pacz: https://www.academia.edu/29461542 *)

Module LepszeRoseTree.

Inductive RoseTree (A : Type) : Type :=
| L : A -> RoseTree A
| N : list (RoseTree A) -> RoseTree A.

Scheme RoseTree_ind' := Induction for RoseTree Sort Prop.

End LepszeRoseTree.

(** * Rekursja wyższego rzędu (TODO) *)

(** Pozostaje kwestia rekursji wyższego rzędu. Co to takiego? Ano dotychczas
    wszystkie nasze wywołania rekurencyjne były konkretne, czyli zaaplikowane
    do argumentów.

    Mogłoby się wydawać, że jest to jedyny możliwy sposób robienia wywołań
    rekurencyjnych, jednak nie jest tak. Wywołania rekurencyjne mogą mieć
    również inną, wyższorzędową postać, a mianowicie - możemy przekazać
    funkcję, którą właśnie definiujemy, jako argument do innej funkcji.

    Dlaczego jest to wywołanie rekurencyjne, skoro nie wywołujemy naszej
    funkcji? Ano dlatego, że tamta funkcja, która dostaje naszą jako
    argument, dostaje niejako możliwość robienia wywołań rekurencyjnych.
    W zależności od tego, co robi tamta funkcja, wszystko może być ok (np.
    gdy ignoruje ona naszą funkcję i w ogóle jej nie używa) lub śmiertelnie
    niebezpieczne (gdy próbuje zrobić wywołanie rekurencyjne na strukturalnie
    większym argumencie).

    Sztoby za dużo nie godoć, bajszpil: *)

Inductive Tree (A : Type) : Type :=
| Node : A -> list (Tree A) -> Tree A.

Arguments Node {A} _ _.

(** [Tree] to typ drzew niepustych, które mogą mieć dowolną (ale skończoną)
    ilość poddrzew. Spróbujmy zdefiniować funkcję, która zwraca lustrzane
    odbicie drzewa. *)

Fixpoint mirror {A : Type} (t : Tree A) {struct t} : Tree A :=
match t with
| Node x ts => Node x (rev (map mirror ts))
end.

(** Nie jest to zbyt trudne. Rekurencyjnie odbijamy wszystkie poddrzewa za
    pomocą [map mirror], a następnie odwracamy kolejność poddrzew z użyciem
    [rev]. Chociaż poszło gładko, to mamy tu do czynienia z czymś, czego
    wcześniej nie widzieliśmy. Nie ma tu żadnego wywołania rekurencyjnego,
    a mimo to funkcja działa ok. Dlaczego? Właśnie dlatego, że wywołania
    rekurencyjne są robione przez funkcję [map]. Mamy więc do czynienia z
    rekursją wyższego rzędu. *)

Inductive mirrorG {A : Type} : Tree A -> Tree A -> Prop :=
| mirrorG_0 :
    forall (x : A) (ts rs : list (Tree A)),
      mirrorsG ts rs -> mirrorG (Node x ts) (Node x (rev rs))

with mirrorsG {A : Type} : list (Tree A) -> list (Tree A) -> Prop :=
| mirrorsG_nil :
    mirrorsG [] []
| mirrorsG_cons :
    forall (t t' : Tree A) (ts ts' : list (Tree A)),
      mirrorG t t' -> mirrorsG ts ts' ->
        mirrorsG (t :: ts) (t' :: ts').

Require Import Equality.

Lemma mirrorG_correct :
  forall {A : Type} (t : Tree A),
    mirrorG t (mirror t).
Proof.
  fix IH 2.
  destruct t. cbn. constructor.
  induction l as [| t ts].
    cbn. constructor.
    cbn. constructor.
      apply IH.
      apply IHts.
Qed.

Compute mirror (Node 0 [Node 1 [Node 5 []; Node 6 []; Node 7 []]; Node 2 []; Node 3 []]).

Module mirror.

Inductive mirrorD {A : Type} : Tree A -> Type :=
| mirrorD' :
    forall (x : A) (ts : list (Tree A)),
      mirrorsD (rev ts) -> mirrorD (Node x ts)

with mirrorsD {A : Type} : list (Tree A) -> Type :=
| mirrorsD_nil : mirrorsD []
| mirrorsD_cons :
    forall (t : Tree A) (ts : list (Tree A)),
      mirrorD t -> mirrorsD ts -> mirrorsD (t :: ts).

Inductive mapG
  {A B : Type} (f : A -> B -> Type) : list A -> list B -> Type :=
| mapG_nil  : mapG f [] []
| mapG_cons :
    forall (a : A) (b : B) (la : list A) (lb : list B),
      f a b -> mapG f la lb -> mapG f (a :: la) (b :: lb).

Inductive mirrorG2 {A : Type} : Tree A -> Tree A -> Prop :=
| mirrorG2' :
    forall (x : A) (ts ts' : list (Tree A)),
      mapG mirrorG2 ts ts' -> mirrorG2 (Node x ts) (Node x (rev ts')).

Lemma mirrorG2_correct :
  forall {A : Type} (t : Tree A),
    mirrorG2 t (mirror t).
Proof.
  fix IH 2.
  destruct t. cbn. constructor.
  induction l as [| t ts].
    cbn. constructor.
    cbn. constructor.
      apply IH.
      apply IHts.
Qed.

End mirror.

(** * Reguły indukcji dla typów zagnieżdżonych *)

Inductive RoseTree (A : Type) : Type :=
| E : RoseTree A
| N : A -> list (RoseTree A) -> RoseTree A.

Arguments E {A}.
Arguments N {A} _ _.

(** Rzućmy okiem na powyższy typ drzew różanych. Elementy tego typu są albo
    puste, albo są węzłami, które trzymają element typu [A] i listę poddrzew.

    A jak się ma reguła indukcji, którą Coq wygenerował nam dla tego typu?
    Mogłoby się wydawać, że jest najzwyczajniejsza w świecie, ale nic bardziej
    mylnego. *)

Check RoseTree_ind.
(* ===>
  RoseTree_ind :
    forall (A : Type) (P : RoseTree A -> Prop),
      P E ->
      (forall (a : A) (l : list (RoseTree A)), P (N a l)) ->
        forall r : RoseTree A, P r
*)

(** Jeśli dobrze się przyjrzeć tej regule, to widać od razu, że nie ma w niej
    żadnej ale to żadnej indukcji. Są tylko dwa przypadki bazowe: jeden dla
    drzewa pustego, a drugi dla węzła z dowolną wartością i dowolną listą
    poddrzew.

    Dzieje się tak dlatego, że induktywne wystąpienie typu [RoseTree A] jest
    zawinięte w [list], a Coq nie potrafi sam z siebie wygenerować czegoś w
    stylu "jedna hipoteza indukcyjna dla każdego drzewa t z listy ts". Musimy
    mu w tym pomóc!
*)

Print Forall.
(* ===>
Inductive Forall (A : Type) (P : A -> Prop) : list A -> Prop :=
| Forall_nil : Forall P [[]]
| Forall_cons :
    forall (x : A) (l : list A),
      P x -> Forall P l -> Forall P (x :: l).
*)

(** W tym celu przyda nam się induktywnie zdefiniowany predykat [Forall].
    Jeżeli [Forall P l] zachodzi, to każdy element listy [l] spełnia predykat
    [P]. Definicja jest prosta: każdy element pustej listy spełnia [P], a jeżeli
    głowa spełnia [P] i każdy element ogona spełnia [P], to każdy element całej
    listy spełnia [P].

    Dzięki [Forall] możemy już bez trudu wyrazić myśl "dla każdego elementu
    listy mamy hipotezę indukcyjną". Nie pozostaje nic innego, jak sformułować
    i udowodnić porządną regułę indukcji.
*)

Fixpoint RoseTree_ind'
  {A : Type} (P : RoseTree A -> Prop)
  (P_E : P E)
  (P_N : forall (v : A) (ts : list (RoseTree A)), Forall P ts -> P (N v ts))
  (t : RoseTree A) : P t.
Proof.
  destruct t as [| v ts].
  - exact P_E.
  - apply P_N.
    induction ts as [| t ts' IH].
    + constructor.
    + constructor.
      * exact (RoseTree_ind' A P P_E P_N t).
      * exact IH.
Defined.

(** Nasza reguła ma się następująco. Będziemy jej używać do dowodzenia, że każde
    drzewo różane [t] spełnia predykat [P : RoseTree A -> Prop] pod warunkiem, że:
    - drzewo puste spełnia [P]
    - jeżeli każde drzewo z listy [ts] spełnia [P], to dla dowolnego [v : A]
      drzewo [N v ts] również spełnia [P] *)

(** Dowód jest dość prosty. Zauważmy, że zaczyna się on od komendy [Fixpoint],
    ale mimo tego nie piszemy termu, ale odpalamy tryb dowodzenia. Wobec tego
    [RoseeTree_ind'] pojawia się w naszym kontekście jako hipoteza indukcyjna.

    Zaczynamy od rozbicia [t]. Gdy jest puste, kończymy hipotezą [P_E]. Gdy
    jest węzłem, używamy hipotezy [P_N]. Teraz trzeba udowodnić [Forall P ts],
    ale trochę nie ma jak - nasza hipoteza indukcyjna nam w tym nie pomoże, a
    [P_E] i [P_N] też nie za bardzo.

    Kluczową obserwacją w tym momencie jest, że [Forall P ts] jest zdefiniowany
    induktywnie i ma taki sam kształt, jak lista [ts] ([Forall P ts] to w sumie
    "udekorowanie" listy [ts] dowodami [P] dla poszczególnych elementów), więc
    powinniśmy rozumować przez indukcję po [ts].

    W obu przypadkach używamy konstruktora. Pierwszy jest banalny, zaś drugi
    generuje dwa kolejne podcele. W pierwszym używamy naszej "oryginalnej"
    hipotezy induktywnej [RoseTree_ind'], a w drugim hipotezy indukcyjnej
    pochodzącej z indukcji po liście [ts], którą nazwaliśmy [IH]. To kończy
    dowód.
*)

Fixpoint map {A B : Type} (f : A -> B) (t : RoseTree A) : RoseTree B :=
match t with
| E => E
| N v ts => N (f v) (List.map (map f) ts)
end.

(** Zobaczmy jeszcze tylko, jak użyć naszej nowitukiej reguły indukcji. W tym
    celu zdefiniujemy funkcję [map], analogiczną do tej dla list i innych rodzajów
    drzew, która są ci znane, oraz udowodnimy, że mapowanie identyczności to
    to samo co identyczność.
*)

Lemma map_id :
  forall {A : Type} (t : RoseTree A),
    map (fun x => x) t = t.
Proof.
  induction t using @RoseTree_ind'; cbn; [easy |].
  f_equal.
  induction H; cbn; [easy |].
  now rewrite H, IHForall.
Qed.

(** Dowód jest bardzo prosty. Zaczynamy przez indukcję po [t], używając naszej
    nowiutkiej reguły indukcji. Żeby użyć reguły indukcji innej niż domyślna,
    podajemy jej nazwę w klauzuli [using]. Zauważmy też, że musimy poprzedzić
    nazwę reguły indukcji symbolem [@], który sprawia, że argumenty domyślne
    przestają być domyślne. Jeżeli tego nie zrobimy, to Coq powie nam, że nie
    wie, skąd ma wziąć argument [A] (który nie został jeszcze wprowadzony do
    kontekstu).

    Przypadek bazowy jest łatwy, co ilustruje użycie taktyki [easy]. Ponieważ
    [id v = v], to wystarczy teraz pokazać, że twierdzenie zachodzi dla każdego
    drzewa z listy drzew [ts]. Chcemy w tym celu użyć hipotezy indukcyjnej [H],
    ale nie załatwia ona sprawy bezpośrednio: głosi ona, że zmapowanie [id] po
    każdym drzewie z [ts] daje oryginalne drzewo, ale nasz cel jest postaci
    [List.map (map id) ts = ts].

    Jako, że nie ma nigdzie w bibliotece standardowej odpowiedniego lematu,
    musimy znów wykonać indukcję, tym razem po [H]. Bazowy przypadek indukcji
    znów jest łatwy (taktyka [easy]), zaś w przypadku [cons]owym przepisujemy
    [map] w głowie i [List.map (map id)] w ogonie (to jest hipoteza indukcyjna
    z naszej drugiej indukcji) i jest po sprawie.
*)

Lemma map_id' :
  forall {A : Type} (t : RoseTree A),
    map (fun x => x) t = t.
Proof.
  induction t as [| v ts]; cbn; [easy |].
  f_equal.
  induction ts; cbn; [easy |].
  rewrite IHts.
Abort.

(** Zerknijmy jeszcze, co się stanie, jeżeli spróbujemy użyć autogenerowanej
    reguły indukcji. Początek dowodu przebiega tak samo, ale nie mamy do
    dyspozycji żadnych hipotez indukcyjnych, więc drugą indukcję robimy po
    [ts]. Jednak hipoteza indukcyjna z tej drugiej indukcji wystarcza nam
    jedynie do przepisania w ogonie, ale w głowie pozostaje [map id a],
    którego nie mamy czym przepisać. A zatem reguła wygenerowana przez Coqa
    faktycznie jest za mało ogólna.
*)

(** ** Podsumowanie *)

(** Podsumowując: Coq nie radzi sobie z generowaniem reguł indukcji dla
    zagnieżdżonych typów induktywnych, czyli takich, w których definiowany
    typ występuje jako argument innego typu, jak np. [list] w przypadku
    [RoseTree].

    Żeby rozwiązać ten problem, musimy sami sformułować i udowodnić sobie
    bardziej adekwatną regułę indukcji. W tym celu musimy dla zagnieżdżającego
    typu (czyli tego, w którym występuje definiowany przez nas typ, np. [list]
    dla [RoseTree]) zdefiniować predykat [Forall], który pozwoli nam wyrazić,
    że chcemy mieć hipotezę indukcją dla każdego jego elementu. Dowód reguły
    indukcji jest dość prosty i przebiega przez zagnieżdżoną indukcję - na
    zewnątrz w postaci komendy [Fixpoint], a wewnątrz w postaci indukcji po
    dowodzie [Forall].

    Powstałej w ten sposób reguły indukcji możemy używać za pomocą komendy
    [induction ... using ...], przy czym zazwyczaj i tak będziemy musieli
    użyć jeszcze jednej zagnieżdżonej indukcji, żeby cokolwiek osiągnąć.
*)

(** ** Papiery *)

(** Generowanie reguł indukcji dla zagnieżdżonych typów induktywnych:
    #<a class='link' href='https://www.ps.uni-saarland.de/~ullrich/bachelor/thesis.pdf'>
    Generating Induction Principles for Nested Inductive Types in MetaCoq</a>#

    Patrz też: #<a class='link' href='https://hal.inria.fr/hal-01897468/document'>
    Deriving proved equality tests in Coq-elpi: Stronger induction principles for
    containers in Coq</a># (unarna translacja parametryczna)
*)

(** * Metoda induktywnej dziedziny dla typów zagnieżdżonych (TODO) *)

Require Import Recdef.

Fail Functional Scheme map_ind := Induction for map Sort Prop.

Inductive R {A B : Type} (f : A -> B) : RoseTree A -> RoseTree B -> Prop :=
| R_E : R f E E
| R_N  :
    forall (x : A) (ts : list (RoseTree A)) (ts' : list (RoseTree B)),
      Rs f ts ts' -> R f (N x ts) (N (f x) ts')

with
  Rs {A B : Type} (f : A -> B)
    : list (RoseTree A) -> list (RoseTree B) -> Prop :=
| Rs_nil  : Rs f [] []
| Rs_cons :
    forall
      (ta : RoseTree A) (tb : RoseTree B)
      (tsa : list (RoseTree A)) (tsb : list (RoseTree B)),
        R f ta tb -> Rs f tsa tsb -> Rs f (ta :: tsa) (tb :: tsb).

Module v2.

Inductive R {A B : Type} (f : A -> B) : RoseTree A -> RoseTree B -> Prop :=
| R_E : R f E E
| R_N  :
    forall (x : A) (ts : list (RoseTree A)) (ts' : list (RoseTree B)),
      Forall2 (R f) ts ts' -> R f (N x ts) (N (f x) ts').

Lemma correct :
  forall {A B : Type} (f : A -> B) (ta : RoseTree A) (tb : RoseTree B),
    R f ta tb -> map f ta = tb.
Proof.
  fix IH 6.
  destruct 1; cbn; [easy |].
  induction H; cbn; [easy |].
  do 2 f_equal.
  - now apply IH.
  - now congruence.
Defined.

Lemma complete :
  forall {A B : Type} (f : A -> B) (ta : RoseTree A) (tb : RoseTree B),
    map f ta = tb -> R f ta tb.
Proof.
  fix IH 4.
  destruct ta as [| a tas]; cbn; intros tb <-.
  - now constructor.
  - constructor.
    induction tas as [| ta tas' IH']; cbn.
    + now constructor.
    + constructor.
      * now apply IH.
      * easy.
Defined.

End v2.