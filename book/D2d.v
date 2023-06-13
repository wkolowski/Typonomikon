(** * D2d: Typy zagnieżdżone [TODO] *)

Require Import List.
Import ListNotations.

From Typonomikon Require Import D2c.

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