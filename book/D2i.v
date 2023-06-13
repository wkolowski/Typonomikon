(** * D2i: Indukcja wykresowa *)

Require Import List.
Import ListNotations.

Require Import Arith Lia.

From Typonomikon Require Import D5 D2h.

(** * Indukcja wykresowa *)

(** Skoro nie dla psa kiełbasa, to musimy znaleźć jakiś sposób na
    udowodnienie równania rekurencyjnego dla [div]. Zamiast jednak głowić
    się nad równaniami rekurencyjnymi albo nad funkcją [div], zastanówmy
    się w pełnej ogólności: jak dowodzić właściwości funkcji rekurencyjnych?

    No przez indukcję, czy to nie oczywiste? Jasne, ale jak dokładnie owa
    indukcja ma wyglądać? Odpowiedź jest prostsza niż można się spodziewać.
    Otóż gdy kupujesz but, ma on pasować do twojej stopy, zaś gdy kupujesz
    gacie, mają one pasować do twojej dupy. Podobnie jest z indukcją: jej
    kształt ma pasować do kształtu rekursji, za pomocą której zdefiniowana
    została funkcja.

    Czym jest "kształt" rekursji (i indukcji)? Jest to raczej poetyckie
    pojęcie, które odnosi się do tego, jak zdefiniowano funkcję - ile
    jest przypadków, podprzypadków, podpodprzypadków etc., w jaki sposób
    są w sobie zagnieżdżone, gdzie są wywołania rekurencyjne, ile ich
    jest i na jakich argumentach etc.

    Dowiedziawszy się, czym jest kształt rekursji i indukcji, powinniśmy
    zacząć szukać sposobu na dopasowanie kształtu indukcji w naszych
    dowodach do kształtu rekursji funkcji. Dotychczas indukcję zawsze
    robiliśmy po argumencie głównym, zaś z potencjalnymi niedopasowaniami
    kształtów radziliśmy sobie robiąc ad hoc analizy przypadków, które
    uznaliśmy za stosowne.

    I tutaj przyda nam się nieco konceptualnej spostrzegawczości. Zauważyć
    nam bowiem trzeba, że robiąc indukcję po argumencie głównym, kształt
    indukcji odpowiada kształtowi typu argumentu głównego. Skoro zaś mamy
    dopasować go do kształtu rekursji funkcji, to nasuwa nam się oczywiste
    pytanie: czy da się zdefiniować typ, który ma taki sam kształt, jak
    definicja danej funkcji?

    Odpowiedź brzmi: nie, ale da się zdefiniować rodzinę typów
    (a konkretniej pisząc, rodzinę zdań, czyli relację) o takiej właściwości.
    Owa relacja zwie się wykresem funkcji. Jaki ma to związek z bazgrołami
    znanymi ci ze szkoły (zakładam, że wiesz, że wykresem funkcji liniowej
    jest prosta, wykresem funkcji kwadratowej jest parabola, a wykresy sinusa
    i cosinusa to takie wesołe szlaczki)?

    To, co w szkole nazywa się wykresem funkcji, jest jedynie graficznym
    przedstawieniem prawdziwego wykresu, czyli relacji. Samo słowo "wykres",
    wywodzące się w oczywisty sposób od kreślenia, sugeruje, że myślenie o
    wykresie jak o obrazku było pierwsze, a koncepcja wykresu jako relacji
    jest późniejsza.

    W ramach ciekawostki być może warto napisać, że w dawnych czasach
    matematycy silnie utożsamiali funkcję z jej wykresem (w sensie
    obrazka) i przez to byty, których wykresu nie dało się narysować,
    nie były uznawane za funkcje.

    W nieco późniejszym czasie zaszły jednak niemałe zmiany i obecnie
    panującym zabobonem jest utożsamianie funkcji z wykresem (w sensie
    relacji), przez co za funkcje uznawane są także byty, których nie
    da się obliczyć lub nikt nie potrafi pokazać, że terminują (takich
    jak np. "funkcja" Collatza).

    Gdybyś zgłupiał od powyższych czterech akapitów, to przypominam, że
    dla nas zawarte w nich pojęcia oznaczają to:
    - Funkcja to byt, którego typem jest [A -> B] lub [forall x : A, B x].
      Można dać jej coś na wejściu i uzyskać wynik na wyjściu, tzn. można
      ją obliczyć. W Coqu wszystkie funkcje prędzej czy później kończą się
      obliczać.
    - Wykres funkcji to relacja opisująca związek argumentu funkcji z jej
      wynikiem. Każda funkcja ma wykres, ale nie każda relacja jest
      wykresem jakiejś funkcji.
    - Jeżeli typy [A] i [B] da się jakoś sensownie narysować, to możemy
      narysować obrazek przedstawiający wykres funkcji.*)

Definition is_graph
  {A B : Type} (f : A -> B) (R : A -> B -> Prop) : Prop :=
    forall (a : A) (b : B), R a b <-> f a = b.

(** Żeby było nam raźniej, tak wygląda formalna definicja stwierdzenia,
    że relacja [R] jest wykresem funkcji [f]. Uwaga: jeżeli funkcja
    bierze więcej niż jeden argument (tzn. ma typ [A1 -> ... -> An -> B]),
    to wtedy do powyższej definicji musimy wrzucić jej zmodyfikowaną
    wersję o typie [A1 * ... * An -> B]. *)

(** **** Ćwiczenie *)

(** Zdefiniuj funkcję [graph_of], która każdej funkcji przyporządkowuje
    jej wykres. Następnie udowodnij, że faktycznie jest to wykres tej
    funkcji. *)

(* begin hide *)
Definition graph_of {A B : Type} (f : A -> B) : A -> B -> Prop :=
  fun (a : A) (b : B) => f a = b.
(* end hide *)

Lemma is_graph_graph_of :
  forall (A B : Type) (f : A -> B),
    is_graph f (graph_of f).
(* begin hide *)
Proof.
  compute. split; trivial.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Wymyśl typy [A] i [B] oraz relację o typie [A -> B -> Prop], która nie
    jest wykresem żadnej funkcji. Następnie udowodnij formalnie, że nie
    mylisz się. *)

(* begin hide *)
Definition complete (_ _ : bool) : Prop := True.

Lemma complete_not_graph :
  forall f : bool -> bool,
    ~ is_graph f complete.
Proof.
  unfold is_graph, complete. intros f H.
  destruct (H true (negb (f true))).
  specialize (H0 I).
  destruct (f true); inversion H0.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Pokaż, że wszystkie wykresy danej funkcji są równoważne w poniższym
    sensie. *)

Lemma graph_unique :
  forall {A B : Type} (f : A -> B) (R S : A -> B -> Prop),
    is_graph f R -> is_graph f S ->
      forall (a : A) (b : B), R a b <-> S a b.
(* begin hide *)
Proof.
  unfold is_graph.
  intros * HR HS; split; intros.
    rewrite HS, <- HR. assumption.
    rewrite HR, <- HS. assumption.
Qed.
(* end hide *)

(** Skoro już wiemy czym są wykresy funkcji, czas nauczyć się definiować
    induktywne wykresy o kształtach odpowiednich dla naszych niecnych
    celów. *)

Check div_eq.
(* ===> div_eq
        : forall n m : nat,
            div n m = if n <? S m then 0 else S (div (n - S m) m) *)

(** Zwróćmy tylko uwagę na fakt, że mówiąc o kształcie rekursji (lub po
    prostu o kształcie definicji) [div] nie mamy na myśli faktycznej
    definicji, która używa rekursji dobrze ufundowanej i jak już wiemy,
    jest dość problematyczna, lecz "docelowej" definicji, którą wyraża
    między innymi równanie rekurencyjne. *)

Inductive divG : nat -> nat -> nat -> Prop :=
| divG_lt : forall {n m : nat}, n < S m -> divG n m 0
| divG_ge :
    forall n m r : nat,
      n >= S m -> divG (n - S m) m r -> divG n m (S r).

(** [div] jest funkcją typu [nat -> nat -> nat], więc jej wykres to relacja
    typu [nat -> nat -> nat -> Prop]. Dwa pierwsze argumenty relacji
    reprezentują wejście, zaś ostatni argument reprezentuje wyjście, tzn.
    chcemy, żeby [divG n m r] było równoważne [div n m = r].

    Z równania rekurencyjnego widać, że mamy dwa przypadki, czyli konstruktory
    też będą dwa. Jeden odpowiada przypadkowi, gdy [n < S m], tzn. dzielna jest
    mniejsza niż dzielnik (pamiętaj, że [div n m] oznacza [n/(m + 1)], żeby
    uniknąć problemów z dzieleniem przez zero). Konkluzją jest wtedy
    [divG n m 0], tzn. argumentami są [n] i [m], zaś wynikiem jest [0].

    Drugi przypadek to przyadek rekurencyjny. Jeżeli [n >= S m], tzn. dzielna
    jest większa lub równa od dzielnika, to konkluzją jest [divG n m (S r)],
    tzn. argumentami są [n] i [m], zaś wynikiem dzielenia jest [S r]. Czym
    jest [r]? Jest ono skwantyfikowane w tym konstruktorze i pojawia się w
    przesłance [divG (n - S m) m r], która mówi, że wynikiem dzielenia
    [n - S m] przez [m] jest [r]. Przesłanka ta jest wykresowym odpowiednikiem
    wywołania rekurencyjnego. *)

(** **** Ćwiczenie *)

(** Mimo, że wszystkie wykresy danej funkcji są równoważne, to zdefiniować
    można je na wiele różnych sposobów. W zależności od sposobu definicja
    może być użyteczna lub nie, np. przy definicjach induktywnych dostajemy
    za darmo regułę indukcji.

    Podaj inną definicję wykresu funkcji [div], która nie używa typów
    induktywnych (ani nie odwołuje się do samej funkcji [div] - to byłoby
    za łatwe). Użyj kwantyfikatora egzystencjalnego, mnożenia, dodawania
    oraz relacji równości (i niczego więcej). Nazwij ją [divG'].

    Na razie nie musisz dowodzić, że wykres faktycznie jest wykresem [div]
    (póki co jest to za trudne), co oczywiście nie znaczy, że wolno ci się
    mylić - uzasadnij nieformalnie, że wykres faktycznie opisuje funkcję
    [div]. Do dowodu formalnego wrócimy później. *)

(* begin hide *)
Definition divG' (n m r : nat) : Prop :=
  exists q : nat, n = r * S m + q.
(* end hide *)

(** Mamy wykres. Fajnie, ale co możemy z nim zrobić? Jeszcze ważniejsze
    pytanie brzmi zaś: co powinniśmy z nim zrobić? *)

Lemma divG_det :
  forall n m r1 r2 : nat,
    divG n m r1 -> divG n m r2 -> r1 = r2.
Proof.
  intros until 1. revert r2.
  induction H; inversion 1; subst.
    reflexivity.
    1-2: lia.
    f_equal. apply IHdivG. assumption.
Qed.

(** Pierwsza czynność po zdefiniowaniu wykresu, którą powinniśmy wykonać,
    to sprawdzenie, czy ów wykres jest relacją deterministyczną. Relacja
    deterministyczna to taka, której ostatni argument jest zdeterminowany
    przez poprzednie.

    Jeżeli wykres jest deterministyczny to dobrze, a jeżeli nie, to definicja
    na pewno jest błędna, bo wykres ma opisywać funkcję, a żadna funkcja nie
    może dla tych samych argumentów dawać dwóch różnych wyników. Relacjom
    deterministycznym (i nie tylko) przyjrzymy się dokładniej w rozdziale o
    relacjach.

    Dowód nie jest zbyt trudny. Robimy indukcję po dowodzie hipotezy
    [divG n m r1], ale musimy pamiętać, żeby wcześniej zgeneralizować
    [r2], bo w przeciwnym przypadku nasza hipoteza indukcyjna będzie
    za mało ogólna. *)

Lemma divG_correct :
  forall n m : nat,
    divG n m (div n m).
Proof.
  apply (well_founded_ind _ _ wf_lt (fun _ => forall m : nat, _)).
  intros n IH m.
  rewrite div_eq. destruct (Nat.ltb_spec0 n (S m)).
    constructor. assumption.
    constructor.
      lia.
      apply IH. lia.
Qed.

(** Kolejna rzecz do udowodnienia to twierdzenie o poprawności, które mówi,
    że [divG] faktycznie jest wykresem [div]. Zauważ, że moglibyśmy równie
    dobrze sformułować je za pomocą [is_graph], ale tak jak wyżej będzie
    praktyczniej.

    Dowód zaczynamy od indukcji dobrze ufundowanej, po czym wprowadzamy
    zmienne do kontekstu i... aj waj, cóż to takiego? Używamy równania
    rekurencyjnego do rozpisania [div], po czym kończymy przez rozważenie
    przypadków.

    Ten dowód pokazuje, że nie udało nam się osiągnąć celu, który sobie
    postawiliśmy, czyli udowodnienia [div_eq] za pomocą specjalnej reguły
    indukcji. Niestety, bez równania rekurencyjnego nie da się udowodnić
    twierdzenia o poprawności. Nie powinniśmy jednak za bardzo się tym
    przejmować - uszy do góry. Póki co dokończmy poszukiwań ostatecznej
    reguły indukcji, a tym nieszczęsnym równaniem rekurencyjnym zajmiemy
    się później. *)

Lemma divG_complete :
  forall n m r : nat,
    divG n m r -> r = div n m.
Proof.
  intros. apply divG_det with n m.
    assumption.
    apply divG_correct.
Qed.

(** Kolejną, ostatnią już rzeczą, którą powinniśmy zrobić z wykresem, jest
    udowodnienie twierdzenia o pełności, które głosi, że jeżeli argumentom
    [n] i [m] odpowiada na wykresie wynik [r], to [r] jest równe [div n m].
    Dowód jest banalny i wynika wprost z twierdzeń o determinizmie i
    poprawności.

    I po co nam to było? Ano wszystkie fikołki, które zrobiliśmy, posłużą
    nam jako lematy do udowodnienia reguły indukcji wykresowej dla [div].
    Co to za reguła, jak wygląda i skąd ją wziąć? *)

Check divG_ind.
(* ===>
  divG_ind :
    forall
      P : nat -> nat -> nat -> Prop,
      (forall n m : nat, n < S m -> P n m 0) ->
      (forall n m r : nat,
          n >= S m -> divG (n - S m) m r ->
            P (n - S m) m r -> P n m (S r)) ->
        forall n m r : nat, divG n m r -> P n m r *)

(** Pierwowzorem reguły indukcji wykresowej dla danej funkcji jest reguła
    indukcji jej wykresu. Reguła indukcji dla [div] to w sumie to samo co
    powyższa reguła, ale z [r] wyspecjalizowanym do [div n m]. Chcemy też
    pozbyć się niepotrzebnej przesłanki [divG n m r] (po podstawieniu za
    [r] ma ona postać [divG n m (div n m)]), gdyż nie jest potrzebna -
    jest zawsze prawdziwa na mocy twierdzenia [divG_correct]. *)

Lemma div_ind :
  forall
    (P : nat -> nat -> nat -> Prop)
    (Hlt : forall n m : nat, n < S m -> P n m 0)
    (Hge :
      forall n m : nat,
        n >= S m -> P (n - S m) m (div (n - S m) m) ->
          P n m (S (div (n - S m) m))),
      forall n m : nat, P n m (div n m).
Proof.
  intros P Hlt Hge n m.
  apply divG_ind.
    assumption.
    intros. apply divG_complete in H0. subst. apply Hge; assumption.
    apply divG_correct.
Qed.

(** Przydałaby się jednak także i filozoficzna interpretacja reguły. Pozwoli
    nam ona dowodzić zdań, które zależą od [n m : nat] i wyniku dzielenia,
    czyli [div n m].

    Są dwa przypadki, jak w docelowej definicji [div]. Gdy [n < S m], czyli
    dzielna jest mniejsza od dzielnika, wystarczy udowodnić [P n m 0], bo
    wtedy [div n m] wynosi [0]. W drugim przypadku, czyli gdy [n >= S m],
    wystarczy udowodnić [P n m (S (div (n - S m) m))] (bo taki jest wynik
    [div n m] dla [n >= S m]) przy założeniu, że [P] zachodzi dla [n - S m],
    [m] oraz [div (n - S m) m], bo takie są argumenty oraz wynik wywołania
    rekurencyjnego.

    Dowód jest prosty. Wprowadzamy zmienne do kontekstu, a następnie za pomocą
    zwykłego [apply] używamy reguły indukcji [divG_ind] - jako rzekło się
    powyżej, reguła [div_ind] nie jest niczym innym, niż lekką przeróbką
    [divG_ind].

    Mamy trzy podcele. Pierwszy odpowiada przesłance [Hlt]. Drugi to
    przesłanka [Hge], ale musimy wszędzie podstawić [div (n' - S m') m']
    za [r] - posłuży nam do tego twierdzenie o pełności. Trzeci to zbędna
    przesłanka [divG n m (div n m)], którą załatwiamy za pomocą twierdzenia
    o poprawności.

    Włala (lub bardziej wykwintnie: voilà)! Mamy regułę indukcji wykresowej
    dla [div]. Zobaczmy, co i jak można za jej pomocą udowodnić. *)

Lemma div_le :
  forall n m : nat,
    div n m <= n.
Proof.
  apply (div_ind (fun n m r : nat => r <= n)); intros.
    apply Nat.le_0_l.
    lia.
Qed.

(** **** Ćwiczenie *)

(** Udowodnij twierdzenie [div_le] za pomocą indukcji dobrze ufundowanej
    i równania rekurencyjnego, czyli bez użycia indukcji wykresowej. Jak
    trudny jest ten dowód w porównaniu do powyższego? *)

Lemma div_le' :
  forall n m : nat,
    div n m <= n.
(* begin hide *)
Proof.
  apply (well_founded_ind _ _ wf_lt (fun n => forall m : nat, _)).
  intros n IH m.
  rewrite div_eq. destruct (Nat.ltb_spec n (S m)).
    apply Nat.le_0_l.
    specialize (IH (n - S m) ltac:(lia) m). lia.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Udowodnij za pomocą indukcji wykresowej, że twój alternatywny
    wykres funkcji [div] z jednego z poprzednich ćwiczeń faktycznie
    jest wykresem [div].

    Następnie udowodnij to samo za pomocą indukcji dobrze ufundowanej i
    równania rekurencyjnego. Która metoda dowodzenia jest lepsza (nie,
    to pytanie nie jest subiektywne - masz udzielić jedynej słusznej
    odpowiedzi). *)

Lemma divG'_div :
  forall n m : nat,
    divG' n m (div n m).
(* begin hide *)
Proof.
  apply (div_ind divG'); unfold divG'; intros.
    exists n. cbn. reflexivity.
    destruct H0 as [q IH]. exists q. cbn. lia.
Qed.
(* end hide *)

Lemma divG'_div' :
  forall n m : nat,
    divG' n m (div n m).
(* begin hide *)
Proof.
  apply (well_founded_ind _ _ wf_lt (fun _ => forall m : nat, _)).
  intros n IH m. unfold divG' in *.
  rewrite div_eq. destruct (Nat.ltb_spec n (S m)).
    exists n. cbn. reflexivity.
    destruct (IH (n - S m) ltac:(lia) m) as [q IHq].
      exists q. cbn. lia.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Napisz funkcję [split] o sygnaturze
    [split (n : nat) {A : Type} (l : list A) : option (list A * list A)],
    która rozdziela listę [l] na blok o długości [n] i resztę listy, lub
    zwraca [None] gdy lista jest za krótka.

    Następnie udowodnij dla tej funkcji regułę indukcji wykresowej i użyj
    jej do udowodnienia kilku lematów.

    Wszystkie te rzeczy przydadzą się nam w jednym z kolejnych zadań. *)

(* begin hide *)
Fixpoint split
  {A : Type} (n : nat) (l : list A) : option (list A * list A) :=
match n, l with
| 0, _ => Some ([], l)
| S _, [] => None
| S n', h :: t =>
  match split n' t with
  | None => None
  | Some (l1, l2) => Some (h :: l1, l2)
  end
end.

Inductive splitG {A : Type} :
  nat -> list A -> option (list A * list A) -> Prop :=
| splitG_0 :
    forall l : list A, splitG 0 l (Some ([], l))
| splitG_1 :
    forall n : nat, splitG (S n) [] None
| splitG_2 :
    forall (n' : nat) (h : A) (t : list A),
      splitG n' t None -> splitG (S n') (h :: t) None
| splitG_3 :
    forall (n' : nat) (h : A) (t l1 l2 : list A),
      splitG n' t (Some (l1, l2)) ->
        splitG (S n') (h :: t) (Some (h :: l1, l2)).

Lemma splitG_det :
  forall (A : Type) (n : nat) (l : list A) (r1 r2 : option (list A * list A)),
    splitG n l r1 -> splitG n l r2 -> r1 = r2.
Proof.
  intros until 1. revert r2.
  induction H;
    inversion 1; subst; try reflexivity;
    specialize (IHsplitG _ H5); congruence.
Qed.

Lemma splitG_correct :
  forall (A : Type) (n : nat) (l : list A),
    splitG n l (split n l).
Proof.
  induction n as [| n']; cbn.
    constructor.
    destruct l as [| h t].
      constructor.
      case_eq (split n' t); intros.
        destruct p. constructor. rewrite <- H. apply IHn'.
        constructor. rewrite <- H. apply IHn'.
Qed.

Lemma splitG_complete :
  forall (A : Type) (n : nat) (l : list A) (r : option (list A * list A)),
    splitG n l r -> r = split n l.
Proof.
  intros. apply splitG_det with n l.
    assumption.
    apply splitG_correct.
Qed.

Lemma split_ind :
  forall
    {A : Type} (P : nat -> list A -> option (list A * list A) -> Prop)
    (H_0 : forall l : list A, P 0 l (Some ([], l)))
    (H_S_nil : forall n' : nat, P (S n') [] None)
    (H_S_cons_None :
      forall (n' : nat) (h : A) (t : list A),
        split n' t = None -> P n' t None -> P (S n') (h :: t) None)
    (H_S_cons_Some :
      forall (n' : nat) (h : A) (t l1 l2 : list A),
        split n' t = Some (l1, l2) -> P n' t (Some (l1, l2)) ->
          P (S n') (h :: t) (Some (h :: l1, l2))),
      forall (n : nat) (l : list A), P n l (split n l).
Proof.
  intros.
  apply splitG_ind.
    assumption.
    assumption.
    clear n l. intros. apply H_S_cons_None.
      apply splitG_complete in H. auto.
      assumption.
    intros. apply H_S_cons_Some.
      apply splitG_complete in H. auto.
      assumption.
    apply splitG_correct.
Qed.
(* end hide *)

Definition lengthOrder {A : Type} (l1 l2 : list A) : Prop :=
  length l1 < length l2.

Lemma wf_lengthOrder :
  forall A : Type, well_founded (@lengthOrder A).
Proof.
  intros. apply (wf_inverse_image _ _ (@length A)). apply wf_lt.
Defined.

Lemma lengthOrder_split_aux :
  forall {A : Type} (n : nat) (l : list A) (l1 l2 : list A),
    split n l = Some (l1, l2) ->
      n = 0  \/ lengthOrder l2 l.
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros.
    left. reflexivity.
    right. destruct l as [| h t]; cbn in *.
      inversion H.
      case_eq (split n' t).
        intros [l1' l2'] H'. rewrite H' in H. inversion H; subst.
          destruct (IHn' t l1' l2 H').
            rewrite H0 in *. cbn in *. inversion H'; subst.
              apply le_n.
            apply Nat.lt_trans with (length t).
              assumption.
              apply le_n.
        intro. rewrite H0 in H. inversion H.
Restart.
  intro A.
  apply (split_ind (fun n l r => forall l1 l2 : list A,
                                   r = Some (l1, l2) -> n = 0 \/ _));
  intros.
    left. reflexivity.
    inversion H.
    inversion H1.
    inversion H1; subst. right. destruct (H0 _ _ eq_refl).
      subst. inversion H. red. cbn. apply le_n.
      red. cbn. eapply Nat.lt_trans.
        exact H2.
        apply le_n.
Qed.
(* end hide *)

Lemma lengthOrder_split :
  forall (n : nat) (A : Type) (l : list A) (l1 l2 : list A),
    split (S n) l = Some (l1, l2) -> lengthOrder l2 l.
(* begin hide *)
Proof.
  intros. destruct (lengthOrder_split_aux _ _ _ _ H).
    inversion H0.
    assumption.
Qed.
(* end hide *)

(** * Metoda induktywnej dziedziny *)

(** Póki co nie jest źle - udało nam się wszakże wymyślić jedyną słuszną
    metodę dowodzenia właściwości funkcji rekurencyjnych. Jednak nasza
    implementacja kuleje przez to nieszczęsne równanie rekurencyjne. Jak
    możemy udowodnić je bez używania indukcji wykresowej?

    Żeby znaleźć odpowiedź na to pytanie, znowu przyda się nam trochę
    konceptualnej jasności. Na czym tak naprawdę polega problem? Jak
    pamiętamy, problem wynika z tego, że definiując [div] przez rekursję
    dobrze ufundowaną musieliśmy jednocześnie dowodzić, że wywołania
    rekurencyjne odbywają się na argumencie mniejszym od argumentu obecnego
    wywołania.

    Tak więc problemem jest połączenie w jednej definicji dwóch dość luźno
    powiązanych rzeczy, którymi są:
    - Docelowa definicja, która określa obliczeniowe zachowanie funkcji.
      Jej manifestacją jest nasze nieszczęsne równanie rekurencyjne. Bywa
      ona czasem nazywana aspektem obliczeniowym (albo algorytmicznym)
      funkcji.
    - Dowód terminacji, który zapewnia, że definicja docelowa jest legalna
      i nie prowadzi do sprzeczności. Jego manifestacją są występujące w
      definicji [div] dowody na to, że wywołanie rekurencyjne ma argument
      mniejszy od obecnego wywołania. Bywa on czasem nazywany aspektem
      logicznym funkcji. *)

(** Pani doktur, mamy diagnozę! Tylko co z nią zrobić? Czy jest jakaś metoda,
    żeby rozdzielić obliczeniowy i logiczny aspekt danej funkcji, a potem
    poskładać je do kupy?

    Pomyślmy najpierw nad aspektem obliczeniowym. Czy da się zdefiniować
    funkcję bezpośrednio za pomocą jej definicji docelowej, czyli równania
    rekurencyjnego? Żeby to zrobić, musielibyśmy mieć możliwość robienia
    rekursji o dokładnie takim kształcie, jaki ma mieć ta funkcja...

    Eureka! Przecież mamy coś, co pozwala nam na rekursję o dokładnie takim
    kształcie, a mianowicie induktywny wykres! Ale przecież wykres wiąże
    ze sobą argumenty i wynik, a my chcemy dopiero zdefiniować coś, co ów
    wynik obliczy... czyli nie eureka?

    Nie do końca. Możemy zmodyfikować definicję wykresu, wyrzucając z
    niej wszystkie wzmianki o wyniku, uzyskując w ten sposób predykat
    będący induktywną charakteryzacją dziedziny naszej funkcji. Dzięki
    niemu możemy zdefiniować zmodyfikowaną wersję funkcji, w której
    dodatkowym argumentem jest dowód na to, że argumenty należą do
    dziedziny.

    Logiczny aspekt funkcji, czyli dowód terminacji, sprowadza się w
    takiej sytuacji do pokazania, że wszystkie argumenty należą do
    dziedziny (czyli spełniają predykat dziedziny). Żeby zdefiniować
    oryginalną funkcję, wystarczy jedynie poskładać oba aspekty do
    kupy, czyli wstawić dowód terminacji do zmodyfikowanej funkcji.

    Żeby nie utonąć w ogólnościach, zobaczmy, jak nasz wspaniały
    wynalazek radzi sobie z dzieleniem. *)

Inductive divD : nat -> nat -> Type :=
| divD_lt : forall n m : nat, n < S m -> divD n m
| divD_ge :
    forall n m : nat,
      n >= S m -> divD (n - S m) m -> divD n m.

(** Tak wygląda predykat dziedziny dla dzielenia. Zauważmy, że tak naprawdę
    to nie jest to predykat, bo bierze dwa argumenty i co więcej nie zwraca
    [Prop], lecz [Type]. Nie będziemy się tym jednak przejmować - dla nas
    [divD] będzie "predykatem dziedziny". Zauważmy też, że nie jest to
    predykat dziedziny dla [div], lecz dla [div'], czyli zupełnie nowej
    funkcji, którą zamierzamy zdefiniować.

    Ok, przejdźmy do konkretów. [div'] ma mieć typ [nat -> nat -> nat],
    a zatem [divD] ma dwa indeksy odpowiadające dwóm argumentom [div'].
    Pierwszy konstruktor głosi, że jeżeli [n < S m], to oba te argumenty
    należą do dziedziny (bo będziemy chcieli w tym przypadku zwrócić [0]).
    Drugi konstruktor głosi, że jeżeli [n >= S m], to para argumentów [n]
    i [m] należy do dziedziny pod warunkiem, że para argumentów [n - S m]
    i [m] należy do dziedziny. Jest tak, gdyż w tym przypadku będziemy
    chcieli zrobić wywołanie rekurencyjne właśnie na [n - S m] oraz [m]. *)

Fixpoint div'_aux {n m : nat} (H : divD n m) : nat :=
match H with
| divD_lt _ _ _ => 0
| divD_ge _ _ _ H' => S (div'_aux H')
end.

(** Dzięki [divD] możemy zdefiniować funkcję [div'_aux], której typem jest
    [forall n m : nat, divD n m -> nat]. Jest to funkcja pomocnicza, która
    posłuży nam do zdefiniowania właściwej funkcji [div'].

    Ponieważ [divD] jest zdefiniowane induktywnie, docelowa definicja [div']
    jest strukturalnie rekurencyjna po argumencie [H : divD n m], mimo że nie
    jest strukturalnie rekurencyjna po [n] ani [m]. To właśnie jest magia
    stojąca za metodą induktywnej dziedziny - możemy sprawić, żeby każda (no,
    prawie), nawet najdziwniejsza rekursja była strukturalnie rekurencyjna po
    dowodzie należenia do dziedziny.

    Definicja jest banalna. Gdy natrafimy na konstruktor [divD_lt], zwracamy
    [0] (bo wiemy, że jednym z argumentów [divD_lt] jest dowód na to, że
    [n < S m]). Jeżeli trafimy na [divD_ge], to wiemy, że [n >= S m], więc
    robimy wywołanie rekurencyjne na [H' : divD (n - S m) m] i dorzucamy do
    wyniku [S].

    W ten sposób zdefiniowaliśmy obliczeniową część [div'], zupełnie nie
    przejmując się kwestią terminacji. *)

Lemma divD_all :
  forall n m : nat, divD n m.
Proof.
  apply (well_founded_rect nat lt wf_lt (fun _ => forall m : nat, _)).
  intros n IH m.
  destruct (le_lt_dec (S m) n).
    apply divD_ge.
      unfold ge. assumption.
      apply IH. abstract lia.
    apply divD_lt. assumption.
Defined.

(** Dowód terminacji jest bliźniaczo podobny do naszej pierwszej definicji
    [div]. Zaczynamy przez rekursję dobrze ufundowaną z porządkiem [lt] (i
    dowodem [wf_lt] na to, że [lt] jest dobrze ufundowany), wprowadzamy
    zmienne do kontekstu, po czym sprawdzamy, który z przypadków zachodzi.

    Jeżeli [n >= S m], używamy konstruktora [divD_ge]. [n >= S m] zachodzi
    na mocy założenia, zaś [n - S m] i [m] należą do dziedziny na mocy
    hipotezy indukcyjnej. Gdy [n < S m], [n] i [m] należą do dziedziny na
    mocy założenia. *)

Definition div' (n m : nat) : nat :=
  div'_aux (divD_all n m).

(** A oto i ostateczna definicja - wstawiamy dowód [divD_all] do funkcji
    pomocniczej [div'_aux] i uzyskujemy pełnoprawną funkcję dzielącą
    [div' : nat -> nat -> nat]. *)

Compute div' 666 7.
(* ===> = 83 : nat *)

(** Jak widać, wynik oblicza się bez problemu. Po raz kolejny przypominam,
    że [div' n m] oblicza [n/(m + 1)], nie zaś [n/m]. Przypominam też, że
    dowód [divD_all] koniecznie musimy zakończyć za pomocą komendy [Defined],
    a nie jak zazwyczaj [Qed], gdyż w przeciwnym przypadku funkcja [div'] nie
    mogłaby niczego obliczyć. *)

(* begin hide *)
(** TODO: sprawdzić, czy różnica między [Qed] i [Defined] została omówiona. *)
(* end hide *)

Lemma divG_div'_aux :
  forall (n m : nat) (d : divD n m),
    divG n m (div'_aux d).
Proof.
  induction d; cbn; constructor; assumption.
Qed.

Lemma divG_correct' :
  forall n m : nat,
    divG n m (div' n m).
Proof.
  intros. apply divG_div'_aux.
Qed.

(** Żeby udowodnić regułę indukcji wykresowej, będziemy potrzebowali tego
    samego co poprzednio, czyli twierdzeń o poprawności i pełności funkcji
    [div'] względem wykresu [divG]. Dowody są jednak dużo prostsze niż
    ostatnim razem.

    Najpierw dowodzimy, że funkcja pomocnicza [div'_aux] oblicza taki wynik,
    jakiego spodziewa się wykres [divG]. Dowód jest banalny, bo indukcja po
    [d : divD n m] ma dokładnie taki kształt, jakiego nam potrzeba. Właściwy
    dowód dla [div'] uzyskujemy przez wyspecjalizowanie [divG_div'_aux] do
    [div']. *)

Lemma divG_complete' :
  forall n m r : nat,
    divG n m r -> r = div' n m.
Proof.
  intros. apply divG_det with n m.
    assumption.
    apply divG_correct'.
Qed.

Lemma div'_ind :
  forall
    (P : nat -> nat -> nat -> Prop)
    (Hlt : forall n m : nat, n < S m -> P n m 0)
    (Hge :
      forall n m : nat, n >= S m ->
        P (n - S m) m (div' (n - S m) m) ->
          P n m (S (div' (n - S m) m))),
      forall n m : nat, P n m (div' n m).
Proof.
  intros P Hlt Hge n m.
  apply divG_ind.
    assumption.
    intros. apply divG_complete' in H0. subst. apply Hge; assumption.
    apply divG_correct'.
Qed.

(** Dowód pełności i dowód reguły indukcji wykresowej są dokładnie takie
    same jak poprzednio. Zauważ, że tym razem zupełnie zbędne okazało się
    równanie rekurencyjne, bez którego nie mogliśmy obyć się ostatnim
    razem. Jednak jeżeli chcemy, możemy bez problemu je udowodnić, i to
    nawet na dwa sposoby. *)

Lemma div'_eq :
  forall n m : nat,
    div' n m = if n <? S m then 0 else S (div' (n - S m) m).
Proof.
  intros. unfold div'. generalize (divD_all n m) as d.
  induction d; cbn.
    rewrite leb_correct.
      reflexivity.
      apply le_S_n. assumption.
    rewrite leb_correct_conv.
      f_equal. apply divG_det with (n - S m) m; apply divG_div'_aux.
      assumption.
Restart.
  intros. apply div'_ind; clear n m; intros; cbn.
    rewrite leb_correct.
      reflexivity.
      abstract lia.
    rewrite leb_correct_conv.
      reflexivity.
      abstract lia.
Qed.

(** Pierwszy, trudniejszy sposób, to zgeneralizowanie [divD_all n m]
    do dowolnego [d] oraz indukcja po [d] (to tak, jakbyśmy najpierw
    udowodnili tę regułę dla [div'_aux], a potem wyspecjalizowali do
    [div']).

    Drugi, łatwiejszy sposób, realizuje nasz początkowy pomysł, od którego
    wszystko się zaczęło: dowodzimy równania rekurencyjnego za pomocą reguły
    indukcji wykresowej. *)

(** **** Ćwiczenie *)

(** Zdefiniuj funkcję [rot], która bierze liczbę [n] oraz listę i zwraca
    listę, w której bloki o długości dokładnie [n + 1] zostały odwrócone,
    np.

    [rot 0 [1; 2; 3; 4; 5; 6; 7] = [1; 2; 3; 4; 5; 6; 7]]

    [rot 1 [1; 2; 3; 4; 5; 6; 7] = [2; 1; 4; 3; 6; 5; 7]]

    [rot 2 [1; 2; 3; 4; 5; 6; 7] = [3; 2; 1; 6; 5; 4; 7]]

    Wskazówka: rzecz jasna użyj metody induktywnej dziedziny. Nie bez
    przyczyny także w jednym z poprzednich zadań kazałem ci zdefiniować
    funkcję [split], która odkraja od listy blok o odpowiedniej długości.

    Następnie zdefiniuj wykres funkcji [rot] i udowodnij jej regułę indukcji
    wykresowej oraz równanie rekurencyjne. Użyj jej, żeby pokazać, że [rot]
    jest inwolucją dla dowolnego [n], tzn. [rot n (rot n l) = l]. Uwaga:
    potrzebne będzie trochę lematów. *)

(* begin hide *)
Module rot.

Inductive rotD {A : Type} (n : nat) : list A -> Type :=
| rotD_None :
    forall l : list A,
      split (S n) l = None -> rotD n l
| rotD_Some :
    forall l l1 l2 : list A,
      split (S n) l = Some (l1, l2) ->
        rotD n l2 -> rotD n l.

Fixpoint rot_aux {A : Type} {n : nat} {l : list A} (d : rotD n l) : list A :=
match d with
| rotD_None _ _ _ => l
| rotD_Some _ _ l1 _ _ d' => rev l1 ++ rot_aux d'
end.

Lemma rotD_all :
  forall {A : Type} (n : nat) (l : list A), rotD n l.
Proof.
  intros A n.
  apply (@well_founded_rect _ _ (wf_lengthOrder A) (fun l => _)).
  intros l IH.
  case_eq (split (S n) l).
    intros [l1 l2] H. econstructor 2.
      eassumption.
      apply IH. eapply lengthOrder_split. eassumption.
    intro. constructor. assumption.
Defined.

Definition rot {A : Type} (n : nat) (l : list A) : list A :=
  rot_aux (rotD_all n l).

Compute rot 1 [1; 2; 3; 4; 5; 6; 7].

Inductive rotG {A : Type} (n : nat) : list A -> list A -> Prop :=
| rotG_None :
    forall l : list A,
      split (S n) l = None -> rotG n l l
| rotG_Some :
    forall l l1 l2 r : list A,
      split (S n) l = Some (l1, l2) ->
        rotG n l2 r -> rotG n l (rev l1 ++ r).

Lemma rotG_det :
  forall {A : Type} (n : nat) (l r1 r2 : list A),
    rotG n l r1 -> rotG n l r2 -> r1 = r2.
Proof.
  intros until 1. revert r2.
  induction H; inversion 1; subst; try congruence.
    rewrite H in H2. inversion H2; subst. f_equal.
      apply IHrotG. assumption.
Qed.

Lemma rotG_correct :
  forall {A : Type} (n : nat) (l : list A),
    rotG n l (rot n l).
Proof.
  intros. unfold rot. generalize (rotD_all n l) as d.
  induction d; cbn.
    constructor. assumption.
    econstructor; eauto.
Qed.

Lemma rotG_complete :
  forall (A : Type) (n : nat) (l r : list A),
    rotG n l r -> r = rot n l.
Proof.
  intros. apply rotG_det with n l.
    assumption.
    apply rotG_correct.
Qed.

Lemma rot_ind :
  forall
    (A : Type) (n : nat) (P : list A -> list A -> Prop)
    (H_None :
      forall l : list A,
        split (S n) l = None -> P l l)
    (H_Some :
      forall l l1 l2 : list A,
        split (S n) l = Some (l1, l2) ->
          P l2 (rot n l2) -> P l (rev l1 ++ rot n l2)),
    forall l : list A, P l (rot n l).
Proof.
  intros.
  apply rotG_ind with n.
    assumption.
    intros. apply rotG_complete in H0. subst. apply H_Some; assumption.
    apply rotG_correct.
Qed.

Lemma rot_eq :
  forall {A : Type} (n : nat) (l : list A),
    rot n l =
    match split (S n) l with
    | None => l
    | Some (l1, l2) => rev l1 ++ rot n l2
    end.
Proof.
  intros A n.
  apply (rot_ind A n (fun l r => r = _)); intros.
    rewrite H. reflexivity.
    rewrite H. reflexivity.
Qed.

Lemma split_spec :
  forall {A : Type} (n : nat) (l l1 l2 : list A),
    split n l = Some (l1, l2) -> length l1 = n /\ l = l1 ++ l2.
Proof.
  intros A.
  apply (split_ind (fun n l r =>
    forall l1 l2, r = Some (l1, l2) -> length l1 = n /\ _));
  intros.
    inversion H; subst. auto.
    inversion H.
    inversion H1.
    inversion H1. specialize (H0 _ _ eq_refl). cbn. subst.
      firstorder congruence.
Qed.

Lemma split_app_length :
  forall {A : Type} (n : nat) (l1 l2 : list A),
    length l1 = n -> split n (l1 ++ l2) = Some (l1, l2).
Proof.
  intro A.
  apply (split_ind (fun n l1 r =>
    forall l2, length l1 = n -> split n (l1 ++ l2) = Some (l1, l2)));
  intros.
    destruct l; inversion H. reflexivity.
    inversion H.
    cbn. rewrite H0.
      reflexivity.
      inversion H1. reflexivity.
    cbn. rewrite H0.
      reflexivity.
      inversion H1. reflexivity.
Qed.

Lemma rot_rot :
  forall {A : Type} (n : nat) (l : list A),
    rot n (rot n l) = l.
Proof.
  intros A n.
  apply (rot_ind A n (fun l r => rot n r = l)); intros.
    rewrite rot_eq, H. reflexivity.
    apply split_spec in H. destruct H. subst.
      rewrite rot_eq, split_app_length.
        rewrite rev_rev, H0. reflexivity.
        rewrite length_rev. assumption.
Qed.

End rot.
(* end hide *)

(** **** Ćwiczenie *)

(** Zdefiniuj funkcję [Eratosthenes : nat -> list nat], która dla
    danego [n] znajduje listę wszystkich liczb pierwszych, które są
    mniejsze lub równe [n].

    Jako funkcję pomocniczą zaimplementuj sito Eratosthenesa. Sito
    to funkcja [sieve : list nat -> list nat], która działa tak:
    - jeżeli wejście jest puste, zwróć listę pustą
    - jeżeli wejście ma głowę [h] i ogon [t], to wstaw [h] na początek
      wyniku i wywołaj się rekurencyjnie na ogonie [t] z odfiltrowanymi
      wszystkimi wielokrotnościami głowy [h]

    Jeżeli jako argument [sieve] podamy listę wszystkich liczb poczynając
    od pewnej liczby pierwszej [p] aż do [n], to otrzymamy listę liczb
    pierwszych między [p] i [n].

    Żeby sprawnie rozwiązać to zadanie, zgeneralizuj funkcję [sieve]
    na dowolny typ [A] i funkcję porównującą [cmp : A -> A -> bool]
    (tak będzie łatwiej) i użyj metody induktywnej dziedziny. *)

(* begin hide *)
Module sieve.

Inductive D {A : Type} (f : A -> A -> bool) : list A -> Type :=
| D0 : D f []
| D1 : forall (h : A) (t : list A),
         D f (filter (f h) t) -> D f (h :: t).

Arguments D0 {A f}.
Arguments D1 {A f} _ _ _.

Lemma D_all :
  forall (A : Type) (f : A -> A -> bool) (l : list A), D f l.
Proof.
  intros A f.
  apply (well_founded_rect _ _ (wf_lengthOrder A)).
  destruct x as [| h t]; intros IH.
    constructor.
    constructor. apply IH. clear IH. induction t as [| h' t']; cbn.
      constructor.
      destruct (f h h'); cbn in *.
        apply le_n_S. apply IHt'.
        apply le_S. apply IHt'.
Defined.

Fixpoint sieve'
  {A : Type} (f : A -> A -> bool)
  {l : list A} (d : D f l) : list A :=
match d with
| D0 => []
| D1 h t d' => h :: sieve' f d'
end.

Definition sieve
  {A : Type} (f : A -> A -> bool) (l : list A) : list A :=
    sieve' f (D_all A f l).

(**
TODO: zrobić porządek z [list] i [Datatypes.list], najlepiej po
TODO: prostu usunąć definicję [list] z rozdziału D5.
*)

Fixpoint any {A : Type} (f : A -> bool) (l : list A) : bool :=
match l with
| [] => false
| h :: t => f h || any f t
end.

Fixpoint iterate {A : Type} (f : A -> A) (x : A) (n : nat) : list A :=
match n with
| 0 => []
| S n' => x :: iterate f (f x) n'
end.

Definition divides (n m : nat) : bool :=
  any (fun k : nat => n * k =? m) (iterate S 0 (S m)).

Definition Eratosthenes (n : nat) : list nat :=
  sieve (fun n m => negb (divides n m)) (iterate S 2 n).

Compute Eratosthenes 100.

End sieve.
(* end hide *)

(** * Komenda [Function] *)

(** Odkryliśmy uniwersalną metodę definiowania funkcji i dowodzenia ich
    właściwości. Czego chcieć więcej?

    Po pierwsze, metoda definiowania nie jest uniwersalna (jeszcze), o czym
    przekonamy się w kolejnych podrozdziałach. Po drugie, mimo że metoda
    dowodzenia faktycznie jest uniwersalna, to komu normalnemu chciałoby
    się przy każdej funkcji tyle pisać? Jakieś wykresy, dziedziny, lematy,
    reguły indukcji, co to ma być?

    Czy w celu sprawnego definiowania i dowodzenia właściwości funkcji trzeba
    zoutsourcować cały proces i zatrudnić milion Hindusów? Na szczęście nie,
    gdyż bóg dał nam komendę [Function]. *)

Require Import Recdef.

(** Komenda ta żyje w module [Recdef], którego nazwa jest skrótem od słów
    "recydywista defraudator"... dobra, koniec żartów. *)

Function div'' (n m : nat) {measure id n} : nat :=
  if n <? S m then 0 else S (div'' (n - S m) m).
Proof.
  intros. unfold id. cbn in teq. apply leb_complete_conv in teq. lia.
Defined.
(* ===> div''_tcc is defined
        div''_terminate is defined
        div''_ind is defined
        div''_rec is defined
        div''_rect is defined
        R_div''_correct is defined
        R_div''_complete is defined *)

(** Definicja zaczyna się od słowa kluczowego [Function], następnie mamy
    nazwę funkcji i argumenty, tak jak w zwykłych definicjach za pomocą
    [Definition] czy [Fixpoint], a później tajemniczą klauzulę
    [{measure id n}], do której zaraz wrócimy, i zwracany typ. Ciało
    definicji wygląda dokładnie jak docelowa definicja.

    Jednak po kropce definicja nie kończy się - zamiast tego Coq każe nam
    udowodnić, że wywołanie rekurencyjne [div''] odbywa się na argumencie
    mniejszym niż [n]. Po zakończeniu dowodu funkcja zostaje zaakceptowana
    przez Coqa.

    To jednak nie koniec. Komenda [Function] nie tylko pozwala bezboleśnie
    zdefiniować [div''], ale też generuje dla nas całą masę różnych rzeczy:
    - [div''_tcc] to lemat, który mówi, że wszystkie wywołania rekurencyjne
      są na argumencie mniejszym od obecnego
    - [div''_terminate] to dowód tego, że funkcja terminuje (czyli że się
      nie zapętla). Jeżeli przyjrzysz się jego typowi, to zobaczysz, że
      jest podobny zupełnie do niczego. Wynika to z faktu, że komenda
      [Function] tak naprawdę nie używa metody induktywnej dziedziny, ale
      pewnej innej metody definiowania funkcji ogólnie rekurencyjnych.
      Nie powinno nas to jednak martwić - ważne, że działa.
    - [div''_ind] to reguła indukcji wykresowej dla [div'']. Jest też jej
      wariant [div''_rect], czyli "rekursja wykresowa", służąca raczej do
      definiowania niż dowodzenia.
    - [R_div''] to induktywnie zdefiniowany wykres funkcji [div'']. Zauważ
      jednak, że nie jest on relacją, a rodziną typów - nie wiem po co i
      nie ma co wnikać w takie detale.
    - [R_div''_correct] to twierdzenie o poprawności wykresu.
    - [R_div''_complete] to twierdzenie o pełności wykresu.
    - [div''_equation] to równanie rekurencyjne *)

(** Jak więc widać, nastąpił cud automatyzacji i wszystko robi się samo.
    To jednak nie koniec udogodnień. Zobaczmy, jak możemy udowodnić jakiś
    fakt o [div'']. *)

Lemma div''_le :
  forall n m : nat, div'' n m <= n.
Proof.
  intros. functional induction (div'' n m).
    apply Nat.le_0_l.
    apply leb_complete_conv in e. lia.
Defined.

(** Dowodzenie właściwości funkcji zdefiniowanych za pomocą [Function]
    jest bajecznie proste. Jeżeli wszystkie argumenty funkcji znajdują
    się w kontekście, to możemy użyć taktyki [functional induction
    (nazwa_funkcji argument_1 ... argument_n)], która odpala indukcję
    wykresową dla tej funkcji. Z powodu nazwy tej taktyki indukcja
    wykresowa bywa też nazywana indukcją funkcyjną.

    Wujek Dobra Rada: nigdy nie odwijaj definicji funkcji zdefiniowanych
    za pomocą [Function] ani nie próbuj ręcznie aplikować reguły indukcji
    wykresowej, bo skończy się to jedynie bólem i zgrzytaniem zębów.

    Na koniec wypadałoby jedynie dodać, że wcale nie złapaliśmy pana boga
    za nogi i komenda [Function] nie rozwiązuje wszystkich problemów
    pierwszego świata. W szczególności niektóre funkcje mogą być tak
    upierdliwe, że komenda [Function] odmówi współpracy z nimi. Radzeniu
    sobie z takimi ciężkimi przypadkami poświęcimy kolejne podrozdziały. *)

(** **** Ćwiczenie *)

(** Zdefiniuj funkcję [rot] (i wszystkie funkcje pomocnicze) jeszcze raz,
    tym razem za pomocą komendy [Function]. Porównaj swoje definicje wykresu
    oraz reguły indukcji z tymi automatycznie wygenerowanymi. Użyj taktyki
    [functional induction], żeby jeszcze raz udowodnić, że [rot] jest
    inwolucją. Policz, ile pisania udało ci się dzięki temu zaoszczędzić.

    Czy w twoim rozwiązaniu są lematy, w których użycie indukcji funkcyjnej
    znacznie utrudnia przeprowadzenie dowodu? W moim poprzednim rozwiązaniu
    był jeden taki, ale wynikał z głupoty i już go nie ma. *)

(* begin hide *)
Module rotn_Function.

Function split
  {A : Type} (n : nat) (l : list A)
  : option (list A * list A) :=
match n, l with
| 0, _ => Some ([], l)
| S n', [] => None
| S n', h :: t =>
  match split n' t with
  | None => None
  | Some (l1, l2) => Some (h :: l1, l2)
  end
end.

Lemma split_spec :
  forall {A : Type} (n : nat) (l l1 l2 : list A),
    split n l = Some (l1, l2) -> length l1 = n /\ l = l1 ++ l2.
Proof.
  intros A n l.
  functional induction (split n l); inversion 1; subst; cbn.
    split; reflexivity.
    destruct (IHo _ _ e1). subst. split; reflexivity.
Qed.

Lemma split_app_length :
  forall {A : Type} (n : nat) (l1 l2 : list A),
    length l1 = n -> split n (l1 ++ l2) = Some (l1, l2).
Proof.
  intros A n l.
  functional induction (split n l); inversion 1; subst; cbn.
    rewrite H. cbn. destruct l; inversion H. reflexivity.
    rewrite IHo; reflexivity.
    rewrite IHo; reflexivity.
Qed.

Lemma split_length_aux :
  forall (A : Type) (n : nat) (l l1 l2 : list A),
    split n l = Some (l1, l2) ->
      n = 0 \/ length l2 < length l.
Proof.
  intros A n l.
  functional induction (split n l); inversion 1; subst.
    left. reflexivity.
    right. destruct (IHo _ _ e1).
      subst. cbn in e1. inversion e1; subst. cbn. apply le_n.
      cbn. lia.
Qed.

Lemma split_length :
  forall (A : Type) (n : nat) (l l1 l2 : list A),
    split (S n) l = Some (l1, l2) -> length l2 < length l.
Proof.
  intros. destruct (split_length_aux A (S n) l l1 l2 H).
    inversion H0.
    assumption.
Qed.

Function rot
  {A : Type} (n : nat) (l : list A) {measure length l} : list A :=
match split (S n) l with
| None => l
| Some (l1, l2) => rev l1 ++ rot n l2
end.
Proof.
  intros A n l _ l1 l2 _ H.
  eapply lengthOrder_split. eassumption.
Defined.

Arguments rot {x} _ _.

Compute rot 1 [1; 2; 3; 4; 5; 6; 7].

Lemma rot_rot :
  forall (A : Type) (n : nat) (l : list A),
    rot n (rot n l) = l.
Proof.
  intros. functional induction (rot n l).
    rewrite rot_equation, e. reflexivity.
    apply split_spec in e. destruct e. subst.
      rewrite rot_equation, split_app_length.
        rewrite rev_rev, IHl0. reflexivity.
        rewrite length_rev. assumption.
Qed.

End rotn_Function.
(* end hide *)

(** * Rekursja zagnieżdżona *)

(** Jakież to diabelstwo może być tak diabelskie, by przeciwstawić się
    metodzie induktywnej dziedziny oraz komendzie [Function]? Ano ano,
    rekursja zagnieżdżona - wywołanie rekurencyjne jest zagnieżdżone,
    jeżeli jego argumentem jest wynik innego wywołania rekurencyjnego. *)

Module McCarthy.

Fail Fixpoint f (n : nat) : nat :=
  if 100 <? n then n - 10 else f (f (n + 11)).

Fail Function f (n : nat) {measure id n} : nat :=
  if 100 <? n then n - 10 else f (f (n + 11)).

(** Ta funkcja jest podobna zupełnie do niczego, co dotychczas widzieliśmy.
    Działa ona następująco:
    - jeżeli [n] jest większe od [100], to zwróć [n - 10]
    - w przeciwnym wypadku wywołaj rekurencyjnie [f] na [n + 11], a następnie
      wywołaj [f] na wyniku tamtego wywołania. *)

(** Taka rekursja jest oczywiście nielegalna: [n + 11] nie jest strukturalnym
    podtermem [n], gdyż jest od niego większe, zaś [f (n + 11)] w ogóle nie
    wiadomo a priori, jak się ma do [n]. Nie dziwota więc, że Coq odrzuca
    powyższą definicję.

    Być może wobec tego taka "funkcja" w ogóle nie jest funkcją, a definicja
    jest wadliwa? Otóż nie tym razem. Okazuje się bowiem, że istnieje funkcja
    zachowująca się zgodnie z zawartym w definicji równaniem. Żebyśmy mogli
    w to uwierzyć, zastanówmy się, ile wynosi [f 100].

    [f 100 = f (f 111) = f 101 = 101 - 10 = 91] - poszło gładko. A co z [99]?
    Mamy [f 99 = f (f 110) = f 100 = 91] - znowu 91, czyżby spiseg? Dalej:
    [f 98 = f (f 109) = f 99 = 91] - tak, to na pewno spiseg. Teraz możemy
    zwerbalizować nasze domysły: jeżeli [n <= 100], to [f n = 91]. Jak
    widać, nieprzypadkowo funkcja ta bywa też nazywana "funkcją 91
    McCarthy'ego".

    Czy da się tę funkcję zaimplementować w Coqu? Jeszcze jak! *)

Definition f_troll (n : nat) : nat :=
  if n <=? 100 then 91 else n - 10.

(** Ehhh... nie tego się spodziewałeś, prawda? [f_troll] jest wprawdzie
    implementacją opisanej powyżej nieformalnie funkcji [f], ale definicja
    opiera się na tym, że z góry wiemy, jaki jest wynik [f] dla dowolnego
    argumentu. Nie trzeba chyba tłumaczyć, że dla żadnej ciekawej funkcji
    nie będziemy posiadać takiej wiedzy (a sama funkcja McCarthy'ego nie
    jest ciekawa, bo jest sztuczna, ot co!).

    Czy więc da się zaimplementować [f] bezpośrednio, tzn. w sposób dokładnie
    oddający definicję nieformalną? Otóż tak, da się i to w sumie niewielkim
    kosztem: wystarczy jedynie nieco zmodyfikować naszą metodę induktywnej
    dziedziny. Zanim jednak to zrobimy, zobaczmy, dlaczego nie obejdzie się
    bez modyfikacji. *)

Fail Inductive fD : nat -> Type :=
| fD_gt100 : forall n : nat, 100 < n -> fD n
| fD_le100 :
    forall n : nat, n <= 100 ->
      fD (n + 11) -> fD (f (n + 11)) -> fD n.

(* ===> The command has indeed failed with message:
        The reference f was not found in the current environment. *)

(** A oto i źródło całego problemu. Jeżeli [n <= 100], to chcemy zrobić dwa
    wywołania rekurencyjne: jedno na [n + 11], a drugie na [f (n + 11)].
    Wobec tego należenie tych dwóch argumentów do dziedziny jest warunkiem
    należenia [n] do dziedziny i stąd postać całego konstruktora.

    Niestety, definicja jest zła - [f (n + 11)] nie jest poprawnym termem,
    gdyż [f] nie jest jeszcze zdefiniowane. Mamy więc błędne koło: żeby
    zdefiniować [f], musimy zdefiniować predykat dziedziny [fD], ale żeby
    zdefiniować [fD], musimy zdefiniować [f].

    Jak wyrwać się z tego błędnego koła? Ratunek przychodzi ze strony być
    może nieoczekiwanej, ale za to już bardzo dobrze przez nas poznanej, a
    jest nim induktywna definicja wykresu. Tak tak - w definicji [fD] możemy
    (a nawet musimy) zastąpić wystąpienia [f] przez wystąpienia wykresu [f].

    Hej ho, po przykład by się szło. *)

Inductive fG : nat -> nat -> Prop :=
| fG_gt100 :
    forall n : nat, 100 < n -> fG n (n - 10)
| fG_le100 :
    forall n r1 r2 : nat,
      n <= 100 -> fG (n + 11) r1 -> fG r1 r2 -> fG n r2.

(** Tak wygląda wykres funkcji [f]. Wywołanie rekurencyjne [f (f (n + 11)]
    możemy zareprezentować jako dwa argumenty, mianowicie [fG (n + 11) r1]
    i [fG r1 r2]. Dosłownie odpowiada to wywołaniu rekurencyjnemu w stylu
    [let r1 := f (n + 11) in let r2 := f r1 in r2]. *)

Lemma fG_det :
  forall n r1 r2 : nat,
    fG n r1 -> fG n r2 -> r1 = r2.
Proof.
  intros until 1. revert r2.
  induction H; intros r Hr.
    inversion Hr; subst.
      reflexivity.
      abstract lia.
    inversion Hr; subst.
      abstract lia.
      assert (r1 = r0) by apply (IHfG1 _ H3); subst.
        apply (IHfG2 _ H4).
Defined.

(** Po zdefiniowaniu wykresu dowodzimy, podobnie łatwo jak poprzednio, że
    jest on relacją deterministyczną.*)

Inductive fD : nat -> Type :=
| fD_gt100 :
    forall n : nat, 100 < n -> fD n
| fD_le100 :
    forall n r : nat, n <= 100 ->
      fG (n + 11) r -> fD (n + 11) -> fD r -> fD n.

(** A tak wygląda definicja predykatu dziedziny. Zamiast [fD (f (n + 11))]
    mamy [fD r], gdyż [r] na mocy argumentu [fG (n + 11) r] reprezentuje
    wynik wywołania rekurencyjnego [f (n + 11)]. *)

Fixpoint f' {n : nat} (d : fD n) : nat :=
match d with
| fD_gt100 _ _ => n - 10
| fD_le100 _ _ _ _ _ d2 => f' d2
end.

(** Definicja funkcji pomocniczej [f'] może być nieco zaskakująca: gdzie
    podziało się zagnieżdżone wywołanie rekurencyjne? Nie możemy jednak
    dać się zmylić przeciwnikowi. Ostatnią klauzulę dopasowania do wzorca
    możemy zapisać jako [| fD_le100 n r H g d1 d2 => f' d2]. Widzimy, że
    [d2] jest typu [fD r], ale [g : fG (n + 11) r], więc możemy myśleć,
    że [r] to tak naprawdę [f (n + 11)], a zatem [d2] tak naprawdę jest
    typu [fD (f (n + 11))]. Jeżeli dodatkowo napiszemy wprost domyślny
    argument [f'], to wywołanie rekurencyjne miałoby postać
    [@f' (@f' (n + 11) d1) d2], a więc wszystko się zgadza. Żeby jednak
    nie rzucać słów na wiatr, udowodnijmy to. *)

Lemma f'_correct :
  forall (n : nat) (d : fD n), fG n (f' d).
Proof.
  induction d; cbn.
    constructor. assumption.
    econstructor 2.
      assumption.
      exact IHd1.
      assert (r = f' d1).
        apply fG_det with (n + 11); assumption.
        subst. assumption.
Defined.

(** Dowód twierdzenia o poprawności jest tylko odrobinkę trudniejszy niż
    ostatnio, gdyż w przypadku wystąpienia w kontekście dwóch hipotez o
    typie [fG (n + 11) _] musimy użyć twierdzenia o determinizmie wykresu. *)

Lemma f'_complete :
  forall (n r : nat) (d : fD n),
    fG n r -> f' d = r.
Proof.
  intros. apply fG_det with n.
    apply f'_correct.
    assumption.
Defined.

(** Dowód twierdzenia o pełności pozostaje bez zmian. *)

Lemma fG_le100_spec :
  forall n r : nat,
    fG n r -> n <= 100 -> r = 91.
Proof.
  induction 1; intro.
    abstract lia.
    inversion H0; subst.
      inversion H1; subst.
        assert (n = 100) by abstract lia. subst. reflexivity.
        abstract lia.
      abstract lia.
Defined.

Lemma f'_le100 :
  forall (n : nat) (d : fD n),
    n <= 100 -> f' d = 91.
Proof.
  intros. apply fG_le100_spec with n.
    apply f'_correct.
    assumption.
Defined.

Lemma f'_ge100 :
  forall (n : nat) (d : fD n),
    100 < n -> f' d = n - 10.
Proof.
  destruct d; cbn; abstract lia.
Defined.

(** Teraz następuje mały twist. Udowodnienie, że każdy argument spełnia
    [fD] będzie piekielnie trudne i będziemy w związku z tym potrzebować
    charakteryzacji funkcji [f']. Zaczynamy więc od udowodnienia, że dla
    [n <= 100] wynikiem jest [91]. Najpierw robimy to na wykresie, bo tak
    jest łatwiej, a potem transferujemy wynik na funkcję. Charakteryzację
    dla [100 < n] dostajemy wprost z definicji. *)

Lemma fD_all :
  forall n : nat, fD n.
Proof.
  apply (well_founded_ind _ (fun n m => 101 - n < 101 - m)).
    apply wf_inverse_image. apply wf_lt.
    intros n IH. destruct (le_lt_dec n 100).
      assert (d : fD (n + 11)) by (apply IH; lia).
        apply fD_le100 with (f' d).
          assumption.
          apply f'_correct.
          assumption.
          apply IH. inversion d; subst.
            rewrite f'_ge100.
              abstract lia.
              assumption.
            rewrite f'_le100; abstract lia.
      constructor. assumption.
Defined.

(** Dowód jest przez indukcję dobrze ufundowaną po [n], a relacja dobrze
    ufundowana, której używamy, to [fun n m : nat => 101 - n < 101 - m].
    Dlaczego akurat taka? Przypomnijmy sobie, jak dokładnie oblicza się
    funkcja [f], np. dla [95]:

    [f 95 = f (f 106) = f 96 = f (f 107) = f 97 = f (f 108) = f 98 =
    f (f 109) = f 99 = f (f 110) = f 100 = f (f 111) = f 101 = 91].

    Jak więc widać, im dalej w las, tym bardziej zbliżamy się do magicznej
    liczby [101]. Wyrażenie [101 - n] mówi nam, jak blisko przekroczenia
    [101] jesteśmy, a więc [101 - n < 101 - m] oznacza, że każde wywołanie
    rekurencyjne musi być bliżej [101] niż poprzednie wywołanie. Oczywiście
    zamiast [101] może być dowolna większa liczba - jeżeli zbliżamy się do
    [101], to zbliżamy się także do [1234567890].

    Dowód dobrego ufundowania jest banalny, ale tylko pod warunkiem, że
    zrobiłeś wcześniej odpowiednie ćwiczenie. Jeszcze jedna uwaga: jak
    wymyślić relację dobrze ufundowaną, jeżeli jest nam potrzebna przy
    dowodzie takim jak ten? Mógłbym ci tutaj naopowiadać frazesów o...
    w sumie nie wiem o czym, ale prawda jest taka, że nie wiem, jak się
    je wymyśla. Tej powyższej wcale nie wymyśliłem sam - znalazłem ją w
    świerszczyku dla bystrzaków.

    Dobra, teraz właściwa część dowodu. Zaczynamy od analizy przypadków.
    Drugi przypadek, gdy [100 < n], jest bardzo łatwy. W pierwszym zaś
    przypadku z hipotezy indukcyjnej dostajemy [fD (n + 11)], tzn.
    [n + 11] należy do dziedziny. Skoro tak, to używamy konstruktora
    [fD_le100], a jako [r] (czyli wynik wywołania rekurencyjnego) dajemy
    mu [f' d].

    Dwa podcele zachodzą na mocy założenia, a jedna wynika z twierdzenia
    o poprawności. Pozostaje nam zatem pokazać, że [f' d] także należy do
    dziedziny. W tym celu po raz kolejny używamy hipotezy indukcyjnej. Na
    zakończenie robimy analizę przypadków po [d], używamy charakteryzacji
    [f'] do uproszczenia celu i kończymy rozumowaniami arytmetycznymi. *)

Definition f (n : nat) : nat := f' (fD_all n).

(* Compute f 110. *)

(** Teraz możemy zdefiniować oryginalne [f]. Niestety, funkcja [f] się nie
    oblicza i nie wiem nawet dlaczego. *)

(* begin hide *)
(* TODO: naprawić obliczanie f91, być może winne jest [lia] *)
(* end hide *)

Lemma f_correct :
  forall n : nat, fG n (f n).
Proof.
  intros. apply f'_correct.
Qed.

Lemma f_complete :
  forall n r : nat,
    fG n r -> f n = r.
Proof.
  intros. apply f'_complete. assumption.
Qed.

Lemma f_91 :
  forall (n : nat),
    n <= 100 -> f n = 91.
Proof.
  intros. apply f'_le100. assumption.
Qed.

(** Twierdzenia o poprawności i pełności oraz charakteryzacja dla [f]
    wynikają za darmo z odpowiednich twierdzeń dla [f']. *)

Lemma f_ind :
  forall
    (P : nat -> nat -> Prop)
    (H_gt100 : forall n : nat, 100 < n -> P n (n - 10))
    (H_le100 :
      forall n : nat, n <= 100 ->
        P (n + 11) (f (n + 11)) -> P (f (n + 11)) (f (f (n + 11))) ->
          P n (f (f (n + 11)))),
    forall n : nat, P n (f n).
Proof.
  intros. apply fG_ind.
    assumption.
    intros. apply f_complete in H0. apply f_complete in H2.
      subst. apply H_le100; assumption.
    apply f_correct.
Defined.

(** Reguły indukcji wykresowej dowodzimy tak samo jak poprzednio, czyli za
    pomocą twierdzeń o pełności i poprawności. *)

Lemma f_eq :
  forall n : nat,
    f n = if 100 <? n then n - 10 else f (f (n + 11)).
Proof.
  intros. apply fG_det with n.
    apply f_correct.
    unfold Nat.ltb. destruct (Nat.leb_spec0 101 n).
      constructor. assumption.
      econstructor.
        lia.
        apply f_correct.
        apply f_correct.
Qed.

(** Na koniec również mały twist, gdyż równanie rekurencyjne najprościej jest
    udowodnić za pomocą właściwości wykresu funkcji [f] - jeśli nie wierzysz,
    to sprawdź (ale będzie to bardzo bolesne sprawdzenie).

    Podsumowując: zarówno oryginalna metoda induktywnej dziedziny jak i
    komenda [Function] nie radzą sobie z zagnieżdżonymi wywołaniami
    rekurencyjmi, czyli takimi, w których argumentem jest wynik innego
    wywołania rekurencyjnego. Możemy jednak poradzić sobie z tym problemem
    za pomocą ulepszonej metody induktywnej dziedziny, w której funkcję w
    definicji predykatu dziedziny reprezentujemy za pomocą jej induktywnie
    zdefiniowanego wykresu. *)

(** **** Ćwiczenie *)

(** Przyjrzyjmy się poniższej fikuśnej definicji funkcji: *)

Fail Fixpoint g (n : nat) : nat :=
match n with
| 0 => 0
| S n => g (g n)
end.

(** Wytłumacz, dlaczego Coq nie akceptuje tej definicji. Następnie wymyśl
    twierdzenie charakteryzujące tę funkcję, a na koniec zdefiniuj ją za
    pomocą metody zaprezentowanej w tym podrozdziale. *)

(* begin hide *)

(** Coq odrzuca definicję, bo [g n] nie jest strukturalnym podtermem [S n].

    Charakteryzacja jest prosta: [forall n : nat, g n = 0]. *)

Inductive gG : nat -> nat -> Prop :=
| gG_0 : gG 0 0
| gG_1 : forall n r1 r2 : nat, gG n r1 -> gG r1 r2 -> gG (S n) r2.

Lemma gG_det :
  forall n r1 r2 : nat, gG n r1 -> gG n r2 -> r1 = r2.
Proof.
  intros until 1. revert r2.
  induction H; inversion 1; subst.
    reflexivity.
    specialize (IHgG1 _ H3). subst. apply IHgG2. assumption.
Defined.

Inductive gD : nat -> Type :=
| gD_0 : gD 0
| gD_1 : forall {n r : nat}, gD n -> gG n r -> gD r -> gD (S n).

Fixpoint g' {n : nat} (d : gD n) : nat :=
match d with
| gD_0 => 0
| gD_1 d1 _ d2 => g' d2
end.

Lemma gG_correct' :
  forall (n : nat) (d : gD n),
    gG n (g' d).
Proof.
  induction d; cbn.
    constructor.
    assert (g' d1 = r).
      apply gG_det with n; assumption.
      subst. econstructor; eassumption.
Defined.

Lemma gG_complete' :
  forall (n r : nat) (d : gD n),
    gG n r -> r = g' d.
Proof.
  intros. apply gG_det with n.
    assumption.
    apply gG_correct'.
Defined.

Lemma g'_eq :
  forall (n : nat) (d : gD n), g' d = 0.
Proof.
  induction d; cbn.
    reflexivity.
    assumption.
Defined.

Lemma gD_all :
  forall n : nat, gD n.
Proof.
  induction n as [| n'].
    constructor.
    eapply (gD_1 IHn').
      apply (gG_correct' _ IHn').
      rewrite g'_eq. constructor.
Defined.

Definition g (n : nat) : nat := g' (gD_all n).

Time Compute g 50.

Lemma gG_correct :
  forall n : nat, gG n (g n).
Proof.
  intro. apply gG_correct'.
Qed.

Lemma gG_complete :
  forall n r : nat,
    gG n r -> r = g n.
Proof.
  intros. apply gG_complete'. assumption.
Qed.

Lemma g_ind :
  forall
    (P : nat -> nat -> Prop)
    (P_0 : P 0 0)
    (P_1 :
      forall n : nat, P n (g n) -> P (g n) (g (g n)) -> P (S n) (g (g n))),
    forall n : nat, P n (g n).
Proof.
  intros. apply gG_ind.
    assumption.
    intros. apply gG_complete in H. apply gG_complete in H1. subst.
      apply P_1; assumption.
    apply gG_correct.
Qed.

(* end hide *)

End McCarthy.

(** * Metoda induktywno-rekurencyjnej dziedziny *)

(** Zapoznawszy się z metodą induktywnej dziedziny i jej ulepszoną wersją,
    która potrafi poskromić nawet rekursję zagnieżdżoną, dobrze byłoby na
    koniec podumać sobie trochę, co by było gdyby... Coq raczył wspierać
    indukcję-rekursję?

    Ano, trochę ułatwiłoby to nasze nędzne życie, gdyż metoda induktywnej
    dziedziny przepoczwarzyłaby się w metodę induktywno-rekurencyjnej
    dziedziny: dzięki indukcji-rekursji moglibyśmy jednocześnie zdefiniować
    funkcję (nawet taką, w której jest rekursja zagnieżdżona) jednocześnie
    z jej predykatem dziedziny, co oszczędziłoby nam nieco pisania.

    Zobaczmy, jak to wygląda na przykładzie funkcji McCarthy'ego. Ponieważ
    Coq jednak nie wspiera indukcji-rekursji, będziemy musieli użyć kodowania
    aksjomatycznego, co zapewne nieco umniejszy atrakcyjności tej metody. *)

Module McCarthy'.

(*
Inductive fD : nat -> Type :=
| fD_gt100 : forall n : nat, 100 < n -> fD n
| fD_le100 :
    forall n : nat, n <= 100 ->
      forall d : fD (n + 11), fD (f' (n + 11) d) -> fD n

with Fixpoint f' (n : nat) (d : fD n) : nat :=
match d with
| fD_gt100 n H => n - 10
| fD_le100 n H d1 d2 => f' (f' (n + 11) d1) d2
end.
*)

(** Tak wyglądałoby induktywno-rekurencyjna definicja zmodyfikowanej funkcji
    [f'] wraz z jej dziedziną. Ponieważ w definicji [fD] możemy napisać po
    prostu [fD (f (n + 11) d)], wykres nie jest nam do niczego potrzebny.
    Definicja funkcji wygląda dokładnie tak samo jak ostatnio. *)

Axioms
  (fD : nat -> Type)
  (f' : forall n : nat, fD n -> nat)
  (fD_gt100 : forall n : nat, 100 < n -> fD n)
  (fD_le100 :
    forall n : nat, n <= 100 ->
      forall d : fD (n + 11), fD (f' (n + 11) d) -> fD n)
  (f'_eq1 :
    forall (n : nat) (H : 100 < n), f' n (fD_gt100 n H) = n - 10)
  (f'_eq2 :
    forall
      (n : nat) (H : n <= 100)
      (d1 : fD (n + 11)) (d2 : fD (f' (n + 11) d1)),
        f' n (fD_le100 n H d1 d2) = f' (f' (n + 11) d1) d2)
  (fD_ind :
    forall
      (P : forall n : nat, fD n -> Type)
      (P_gt100 :
        forall (n : nat) (H : 100 < n),
          P n (fD_gt100 n H))
      (P_le100 :
        forall
          (n : nat) (H : n <= 100)
          (d1 : fD (n + 11)) (d2 : fD (f' (n + 11) d1)),
            P (n + 11) d1 -> P (f' (n + 11) d1) d2 ->
              P n (fD_le100 n H d1 d2)),
      {g : forall (n : nat) (d : fD n), P n d |
        (forall (n : nat) (H : 100 < n),
          g n (fD_gt100 n H) = P_gt100 n H) /\
        (forall
          (n : nat) (H : n <= 100)
          (d1 : fD (n + 11)) (d2 : fD (f' (n + 11) d1)),
            g n (fD_le100 n H d1 d2) =
            P_le100 n H d1 d2
              (g (n + 11) d1)
              (g (f' (n + 11) d1) d2))
      }).

(** Aksjomatyczne kodowanie tej definicji działa tak, jak nauczyliśmy się
    w poprzednim rozdziale: najpierw deklarujemy [fD], potem [f], potem
    konstruktory [fD], potem równania definiujące [f], a na samym końcu
    regułę indukcji.

    Reguła indukcji powstaje analogicznie jak dla [slist] z poprzedniego
    rozdziału. Definiujemy tylko jedną rodzinę typów [fD], więc reguła
    da nam tylko jedną funkcję, [g], o typie [forall (n : nat) (d : fD n),
    P n d], gdzie [P : forall n : nat, fD n -> Type] reprezentuje
    przeciwdziedzinę [g].

    Mamy dwa przypadki: nieindukcyjny [P_gt100] odpowiadający konstruktorowi
    [fD_gt100] oraz [P_le100] odpowiadający za [fD_le100], w którym mamy do
    dyspozycji dwie hipotezy indukcyjne. Otrzymana z reguły funkcja spełnia
    oczekiwane równania. *)

Lemma fD_inv :
  forall (n : nat) (d : fD n),
    {H : 100 < n | d = fD_gt100 n H} +
    {H : n <= 100 &
      {d1 : fD (n + 11) &
      {d2 : fD (f' (n + 11) d1) | d = fD_le100 n H d1 d2}}}.
Proof.
  apply fD_ind.
    intros. left. exists H. reflexivity.
    intros. right. exists H, d1, d2. reflexivity.
Defined.

(** Będziemy też chcieli używać [inversion] na hipotezach postaci [fD n],
    ale [fD] nie jest induktywne (tylko aksjomatyczne), więc musimy
    pożądaną przez nas inwersję zamknąć w lemat. Dowodzimy go oczywiście
    za pomocą reguły indukcji. *)

Lemma f_spec :
  forall (n : nat) (d : fD n),
    n <= 100 -> f' n d = 91.
Proof.
  apply (fD_ind (fun n d => n <= 100 -> f' n d = 91)).
    intros n H H'. lia.
    intros n H d1 d2 IH1 IH2 _.
      destruct (fD_inv _ d1) as
            [[H' eq] | (H' & d1' & d2' & eq)].
        destruct (fD_inv _ d2) as
              [[H'' eq'] | (H'' & d1'' & d2'' & eq')].
          rewrite f'_eq2, eq', f'_eq1, eq, f'_eq1 in *.
            clear IH1 eq eq' H' H''. lia.
          rewrite f'_eq2. apply IH2. assumption.
        rewrite f'_eq2. apply IH2. rewrite IH1.
          lia.
          assumption.
Qed.

(** Możemy też udowodnić charakteryzację funkcji [f]. Dowód wygląda dużo
    groźniej niż ostatnio, ale to wszystko wina narzutu związanego z
    aksjomatycznym kodowaniem.

    Dowód idzie tak: najpierw używamy indukcji, a potem naszego inwersjowego
    lematu na hipotezach postaci [fD _ _]. W kluczowych momentach obliczamy
    funkcję [f] za pomocą definiujących ją równań oraz posługujemy się
    taktyką [lia] do przemielenia oczywistych, ale skomplikowanych
    formalnie faktów z zakresu arytmetyki liczb naturalnych. *)

Lemma fD_all :
  forall n : nat, fD n.
Proof.
  apply (well_founded_ind _ (fun n m => 101 - n < 101 - m)).
    apply wf_inverse_image. apply wf_lt.
    intros n IH. destruct (le_lt_dec n 100).
      assert (d : fD (n + 11)) by (apply IH; lia).
        apply fD_le100 with d.
          assumption.
          apply IH. destruct (fD_inv _ d) as [[H eq] | [H _]].
            rewrite eq, f'_eq1. lia.
            rewrite f_spec.
              lia.
              assumption.
      apply fD_gt100. assumption.
Qed.

(** Dowód tego, że wszystkie argumenty spełniają predykat dziedziny, jest
    taki sam jak ostatnio. Jedyna różnica jest taka, że zamiast [inversion]
    musimy ręcznie aplikować [fD_inv]. *)

Definition f (n : nat) : nat := f' n (fD_all n).

Compute f 42.
(* ===> = f' 42 (fD_all 42) : nat *)

(** Mając [f'] oraz dowód [fD_all] możemy zdefiniować [f], które niestety
    się nie oblicza, gdyż [f'] jest dane aksjomatycznie. *)

Lemma f'_ext :
  forall (n : nat) (d1 d2 : fD n),
    f' n d1 = f' n d2.
Proof.
  apply (fD_ind (fun _ d1 => forall d2, _)); intros.
    rewrite f'_eq1. destruct (fD_inv _ d2) as [[H' eq] | [H' _]].
      rewrite eq, f'_eq1. reflexivity.
      lia.
    rewrite f'_eq2. destruct (fD_inv _ d0) as [[H' eq] | (H' & d1' & d2' & eq)].
      lia.
      subst. rewrite f'_eq2. specialize (H0 d1').
        destruct H0. apply H1.
Qed.

(** Żeby udowodnić regułę indukcyjną, potrzebny nam będzie lemat mówiacy,
    że konkretny dowód tego, że [n] spełnia predykat dziedziny [fD], nie
    wpływa na wynik obliczany przez [f']. Dowód jest prosty: używamy
    indukcji po [d1], a następnie inwersji po pozostałych hipotezach,
    przepisujemy równania definiujące [f'] i kończymy za pomocą rozumowań
    arytmetycznych albo hipotezy indukcyjnej. *)

Lemma f_ind :
  forall
    (P : nat -> nat -> Prop)
    (P_gt100 : forall n : nat, 100 < n -> P n (n - 10))
    (P_le100 :
      forall n : nat, n <= 100 ->
        P (n + 11) (f (n + 11)) ->
        P (f (n + 11)) (f (f (n + 11))) ->
          P n (f (f (n + 11)))),
    forall n : nat, P n (f n).
Proof.
  intros. apply (fD_ind (fun n d => P n (f' n d))); intros.
    rewrite f'_eq1. apply P_gt100. assumption.
    rewrite f'_eq2. specialize (P_le100 _ H).
      unfold f in P_le100.
      rewrite !(f'_ext _ _ d1), !(f'_ext _ _ d2) in P_le100.
      apply P_le100; assumption.
Qed.

(** Dowód samej reguły też jest dość prosty. Zaczynamy od indukcji po
    dowodzie faktu, że [n : nat] spełnia predykat dziedziny [fD] (którym
    to dowodem jest [fD_all n], a który schowany jest w definicji [f]).
    W przypadku nierekurencyjnym przepisujemy równanie definiujące [f']
    i kończymy założeniem.

    W przypadku rekurencyjnym również zaczynamy od przepisania definicji
    [f']. Następnie korzystamy z założenia [P_le100], choć technicznie
    jest to dość skomplikowane - najpierw specjalizujemy je częściowo
    za pomocą hipotezy [H], a potem odwijamy definicję [f] i dwukrotnie
    korzystamy z lematu [f'_ext], żeby typy się zgadzały. Po tej obróbce
    możemy śmiało skorzystać z [P_le100] - jej przesłanki zachodzą na mocy
    założenia. *)

(** **** Ćwiczenie *)

(** Rozwiąż jeszcze raz ćwiczenie o funkcji [g] z poprzedniego podrozdziału,
    ale tym razem wykorzystaj metodę induktywno-rekurencyjnej dziedziny
    zaprezentowaną w niniejszym podrozdziale. *)

Fail Fixpoint g (n : nat) : nat :=
match n with
| 0 => 0
| S n => g (g n)
end.

(* begin hide *)

(*
Inductive gD : nat -> Type :=
| gD_0 : gD 0
| gD_S : forall n : nat, gD n -> gD (g n) -> gD (S n)

with Fixpoint g' (n : nat) (d : gD n) : nat :=
match d with
| gD_0 => 0
| gD_S _ d1 d2 => g' (g' n d1) d2
end.
*)

Axioms
  (gD : nat -> Type)
  (g' : forall n : nat, gD n -> nat)
  (gD_0 : gD 0)
  (gD_S : forall (n : nat) (d1 : gD n), gD (g' n d1) -> gD (S n))
  (g'_eq1 : g' 0 gD_0 = 0)
  (g'_eq2 :
    forall (n : nat) (d1 : gD n) (d2 : gD (g' n d1)),
      g' (S n) (gD_S n d1 d2) = g' (g' n d1) d2)
  (gD_ind : forall
    (P : forall n : nat, gD n -> Type)
    (P0 : P 0 gD_0)
    (PS :
      forall (n : nat) (d1 : gD n) (d2 : gD (g' n d1)),
        P n d1 -> P (g' n d1) d2 -> P (S n) (gD_S n d1 d2)),
    {h : forall (n : nat) (d : gD n), P n d |
      h 0 gD_0 = P0 /\
      (forall (n : nat) (d1 : gD n) (d2 : gD (g' n d1)),
        h (S n) (gD_S n d1 d2) =
        PS n d1 d2 (h n d1) (h (g' n d1) d2))
    }).

Lemma g'_char :
  forall (n : nat) (d : gD n), g' n d = 0.
Proof.
  apply gD_ind.
    apply g'_eq1.
    intros. rewrite g'_eq2. assumption.
Qed.

Lemma gD_all :
  forall n : nat, gD n.
Proof.
  induction n as [| n'].
    exact gD_0.
    apply (gD_S n' IHn'). rewrite g'_char. exact gD_0.
Qed.

Definition g (n : nat) : nat := g' n (gD_all n).

Lemma wut :
  forall (n : nat) (d1 d2 : gD n),
    g' n d1 = g' n d2.
Proof.
  apply (gD_ind (fun _ d1 => forall d2, _)); intros.
  (*  destruct (gD_inv d2).*)
Admitted.

Lemma g_ind' :
  forall
    (P : nat -> nat -> Prop)
    (P_0 : P 0 0)
    (P_S :
      forall n : nat, P n (g n) -> P (g n) (g (g n)) -> P (S n) (g (g n))),
    forall n : nat, P n (g n).
Proof.
  intros.
  apply (gD_ind (fun n d => P n (g' n d))).
    rewrite g'_eq1. assumption.
    intros. rewrite g'_eq2. specialize (P_S n0).
      assert (g' n0 d1 = g n0).
        apply wut.
        rewrite <- !H1 in P_S. assert (g (g' n0 d1) = g' (g' n0 d1) d2).
          apply wut.
          rewrite !H2 in *. apply P_S; assumption.
Qed.

(* end hide *)

End McCarthy'.

(** * Metoda induktywnej dziedziny 2 *)

(** Na koniec została nam do omówienia jeszcze jedna drobna kwestia.
    Poznając metodę induktywnej dziedziny, dowiedzieliśmy się, że
    "predykat" dziedziny tak naprawdę wcale nie jest predykatem, ale
    rodziną typów. Czas naprawić ten szkopuł.

    W niniejszym podrozdziale najpierw zapoznamy się (na przykładzie
    dzielenia - znowu) z wariantem metody induktywnej dziedziny, w
    którym dziedzina faktycznie jest predykatem, a na koniec podumamy,
    dlaczego powinno nas to w ogóle obchodzić. *)

Module again.

Inductive divD : nat -> nat -> Prop :=
| divD_lt : forall n m : nat, n < S m -> divD n m
| divD_ge :
    forall n m : nat,
      n >= S m -> divD (n - S m) m -> divD n m.

(** Definicja dziedziny jest taka sama jak ostatnio, ale z tą drobną
    różnicą, że teraz faktycznie jest to predykat.

    Skoro mamy dziedzinę, spróbujmy zdefiniować funkcję pomocniczą
    tak samo jak ostatnio. *)

Fail Fixpoint div_aux {n m : nat} (d : divD n m) : nat :=
match d with
| divD_lt _ _ _ => 0
| divD_ge _ _ _ d' => S (div_aux d')
end.

(* ===> The command has indeed failed with message:
        Incorrect elimination of "d" in the inductive type "divD":
        the return type has sort "Set" while it should be "Prop".
        Elimination of an inductive object of sort Prop
        is not allowed on a predicate in sort Set
        because proofs can be eliminated only to build proofs. *)

(** Cóż, nie da się i nie dziwota - gdyby się dało, to zrobiliśmy tak
    już na samym początku. Powód porażki jest całkiem prozaiczny -
    nie możemy definiować programów przez dopasowanie do wzorca dowodów,
    czyli parafrazując, nie możemy konstruować elementów typów sortów
    [Set] ani [Type] przez eliminację elementów typów sortu [Prop].

    Wynika to z faktu, że sort [Prop] z założenia dopuszcza możliwość
    przyjęcia aksjomatu irrelewancji dowodów (ang. proof irrelevance),
    który głosi, że wszystkie dowody danego zdania są równe. Gdybyśmy
    mogli dopasowywać do wzorca dowody zdań definiując programy,
    irrelewancja wyciekłaby do świata programów i wtedy wszystko byłoby
    równe wszystkiemu, co oczywiście daje sprzeczność.

    Jeżeli powyższy opis nie jest przekonujący, zobaczmy to na szybkim
    przykładzie. *)

Module proof_irrelevance_example.

Inductive bool' : Prop :=
| true' : bool'
| false' : bool'.

(** Najpierw definiujemy typ [bool'], który wygląda jak [bool], ale
    żyje w sorcie [Prop]. *)

Axiom
  proof_irrelevance : forall (P : Prop) (p1 p2 : P), p1 = p2.

(** Następnie przyjmujemy aksjomat irrelewancji dowodów, przez co
    [bool'] staje się tym samym co zdanie [True]. *)

Axioms
  (f : bool' -> bool)
  (eq1 : f true' = true)
  (eq2 : f false' = false).

(** Załóżmy, że Coq pozwolił nam zdefiniować funkcję [f : bool' -> bool],
    która potrafi odróżnić [true'] od [false']. *)

Lemma wut :
  true = false.
Proof.
  rewrite <- eq1.
  rewrite (proof_irrelevance _ _ false').
  rewrite eq2.
  reflexivity.
Qed.

(** Jak widać, [true] to to samo co [f true'], ale [true'] to [false']
    na mocy irrelewancji, a [f false'] to przecież [false]. Konkluzja:
    prawda to fałsz, a tego zdecydowanie nie chcemy. Żeby uniknąć
    sprzeczności, nie wolno definiować programów przez eliminację zdań.

    Od powyższej zasady są jednak wyjątki, mianowicie przy konstrukcji
    programów wolno eliminować dowody zdań, które:
    - nie mają konstruktorów, np. [False]
    - mają jeden konstruktor, którego wszystkie argumenty również są
      dowodami zdań

    Powyższy wyjątek od reguły nazywa się "eliminacją singletonów" i
    jest zupełnie niegroźny, gdyż dla takich zdań możemy bez żadnych
    aksjomatów udowodnić, że wszystkie ich dowody są równe. *)

End proof_irrelevance_example.

(** Dobra, koniec tej przydługiej dygresji. Wracamy do metody induktywnej
    dziedziny, gdzie dziedzina naprawdę jest predykatem. Skoro nie możemy
    zdefiniować funkcji bezpośrednio przez eliminację [d : divD n m], to
    jak inaczej?

    Tutaj ujawnia się pewna chytra sztuczka: nie możemy dopasować [d] za
    pomocą [match]a, ale wciąż możemy robić wywołania rekurencyjne na
    podtermach [d]. Wystarczy więc napisać funkcję, która wyjmuje z [d]
    jego podterm (oczywiście jedynie pod warunkiem, że [n >= S m], bo
    tylko wtedy [d] będzie miało jakiś podterm). Ponieważ kodziedziną
    takiej funkcji będzie [divD (n - S m) m], dopasowanie [d] do wzorca
    będzie już legalne.

    Brzmi... chytrze? Zobaczmy, jak wygląda to w praktyce. *)

Lemma divD_ge_inv :
  forall n m : nat, n >= S m -> divD n m -> divD (n - S m) m.
Proof.
  destruct 2.
    apply Nat.le_ngt in H. contradiction.
    exact H1.
Defined.

(** Jeżeli mamy [d : divD n m] i wiemy, że [n >= S m], to [d] musiało
    zostać zrobione konstruktorem [divD_ge]. Możemy to udowodnić po
    prostu rozbijając [d]. W pierwszym przypadkiem dostajemy sprzeczność
    arytmetyczną (bo [n >= S m] i jednocześnie [n < S m]), zaś w drugim
    wynikiem jest pożądany podterm. *)

Fixpoint div'_aux {n m : nat} (d : divD n m) : nat :=
match le_lt_dec (S m) n with
| right _ => 0
| left H => S (div'_aux (divD_ge_inv n m H d))
end.

(** Żeby zdefiniować [div'_aux] (czyli, przypomnijmy, zmodyfikowaną wersję
    dzielenia, którego argumentem głównym jest [d : divD n m], nie zaś
    samo [n]), sprawdzamy najpierw, czy mamy do czynienia z przypadkiem
    [n < S m], czy z [n >= S m]. W pierwszym przypadku po prostu zwracamy
    [0], zaś w drugim robimy wywołanie rekurencyjne, którego argumentem
    jest [divD_ge_inv n m H d].

    Term ten, jak się okazuje, jest uznawany przez Coqa za podterm [d],
    a więc wywołanie rekurencyjne na nim jest legalne. Dlaczego jest to
    podterm [d]? Jeżeli odwiniemy definicję [divD_ge_inv] i wykonamy
    występujące tam dopasowanie [d] do wzorca, to wiemy, że nie może być
    ono postaci [divD_lt _ _ _], a zatem musi być postaci
    [divD_ge _ _ _ d'] i wynikiem wykonania funkcji jest [d'], które
    faktycznie jest podtermem [d]. *)

Lemma divD_all :
  forall n m : nat, divD n m.
Proof.
  apply (well_founded_rect nat lt wf_lt (fun _ => forall m : nat, _)).
  intros n IH m.
  destruct (le_lt_dec (S m) n).
    apply divD_ge.
      unfold ge. assumption.
      apply IH. abstract lia.
    apply divD_lt. assumption.
Defined.

(** Dowód tego, że każde [n m : nat] należą do dziedziny, jest dokładnie
    taki sam jak poprzednio. *)

Definition div' (n m : nat) : nat :=
  div'_aux (divD_all n m).

Compute div' 666 7.
(* ===> = 83 : nat *)

(** Ostateczna definicja funkcji [div'] również wygląda identycznie jak
    poprzednio i podobnie elegancko się oblicza, a skoro tak, to czas
    udowodnić, że wykresem [div'] jest [divG]. Nie musimy redefiniować
    wykresu - jest on zdefiniowany dokładnie tak samo jak ostatnio. *)

Lemma divG_div'_aux :
  forall (n m : nat) (d : divD n m),
    divG n m (div'_aux d).
Proof.
  Fail induction d.
  (* ===> The command has indeed failed with message:
          Abstracting over the terms "n" and "m" leads to a term
          fun n0 m0 : nat => divG n0 m0 (div'_aux d)
          which is ill-typed. *)
Abort.

(** Pierwsza próba dowodu kończy się zupełnie niespodziewaną porażką
    już przy pierwszym kroku, czyli próbie odpalenia indukcji po [d]. *)

Check divD_ind.
(* ===>
  divD_ind :
    forall P : nat -> nat -> Prop,
    (forall n m : nat, n < S m -> P n m) ->
    (forall n m : nat,
      n >= S m -> divD (n - S m) m -> P (n - S m) m -> P n m) ->
    forall n n0 : nat, divD n n0 -> P n n0
*)

(** Powód jest prosty: konkluzja, czyli [divG n m (div'_aux d)] zależy
    od [d], ale domyślna reguła indukcji wygenerowana przez Coqa, czyli
    [divD_ind], nie jest ani trochę zależna i nie dopuszcza możliwości,
    by konkluzja zależała od [d]. Potrzebna jest więc nam zależna reguła
    indukcji.

    Na szczęście nie musimy implementować jej ręcznie - Coq potrafi
    zrobić to dla nas automatycznie (ale skoro tak, to dlaczego nie
    zrobił tego od razu? - nie pytaj, niezbadane są wyroki...). *)

Scheme divD_ind' := Induction for divD Sort Prop.

(** Do generowania reguł indukcji służy komenda [Scheme]. [divD_ind']
    to nazwa reguły, [Induction for divD] mówi nam, dla jakiego typu
    lub rodziny typów chcemy regułę, zaś [Sort Prop] mówi, że chcemy
    regułę, w której przeciwdziedziną motywu jest [Prop] (tak na
    marginesie - motyw eliminacji to typ lub rodzina typów, której
    element chcemy za pomocą eliminacji skonstruować - powinienem
    był wprowadzić tę nazwę wcześniej). *)

(* begin hide *)
(** TODO: wprowadzić gdzieś wcześniej określenie "motyw eliminacji". *)
(* end hide *)

Check divD_ind'.
(* ===>
  divD_ind' :
    forall P : forall n n0 : nat, divD n n0 -> Prop,
    (forall (n m : nat) (l : n < S m), P n m (divD_lt n m l)) ->
    (forall (n m : nat) (g : n >= S m) (d : divD (n - S m) m),
      P (n - S m) m d -> P n m (divD_ge n m g d)) ->
    forall (n n0 : nat) (d : divD n n0), P n n0 d
*)

(** Jak widać, reguła wygenerowana przez komendę [Scheme] jest zależna,
    gdyż jednym z argumentów [P] jest [divD n n0]. Czas więc wrócić do
    dowodu faktu, że [divG] jest wykresem [div']. *)

Lemma divG_div'_aux :
  forall (n m : nat) (d : divD n m),
    divG n m (@div'_aux n m d).
Proof.
  induction d using divD_ind'.
    unfold div'_aux. destruct (le_lt_dec (S m) n).
      lia.
      constructor. assumption.
    unfold div'_aux. destruct (le_lt_dec (S m) n).
      constructor.
        assumption.
        exact IHd.
      lia.
Qed.

(** Indukcję z użyciem innej niż domyślna reguły możemy zrobić za
    pomocą taktyki [induction d using divD_ind']. Tym razem reguła
    jest wystarczająco ogólna, więc indukcja się udaje.

    Następnym krokiem w obu przypadkach jest odwinięcie definicji
    [div'_aux] i sprawdzenie, czy [n < S m], czy może [n >= S m].
    Taki sposób postępowania jest kluczowy, gdyż próba użycia tu
    taktyki [cbn] skończyłaby się katastrofą - zamiast uprościć
    cel, wyprulibyśmy z niego flaki, które zalałyby nam ekran, a
    wtedy nawet przeczytanie celu byłoby trudne. Jeżeli nie
    wierzysz, spróbuj.

    Mamy więc dowód poprawności [div'_aux] względem wykresu. Wszystkie
    pozostałe dowody przechodzą bez zmian, więc nie będziemy ich tutaj
    powtarzać. *)

End again.

(** Do rozstrzygnięcia pozostaje nam ostatnia już kwestia - po cholerę
    w ogóle bawić się w coś takiego? Powyższe trudności z eliminacją
    [d], dowodzeniem lematów wyciągających z [d] podtermy, dowodzeniem
    przez indukcję po [d], generowaniem lepszych reguł indukcyjnych i
    unikaniem użycia taktyki [cbn] powinny jako żywo uzmysłowić nam,
    że uczynienie dziedziny [divD] prawdziwym predykatem było raczej
    upośledzonym pomysłem.

    Odpowiedź jest krótka i mało przekonująca, a jest nią mechanizm
    ekstrakcji. Cóż to takiego? Otóż Coq dobrze sprawdza się przy
    definiowaniu programów i dowodzeniu ich właściwości, ale raczej
    słabo w ich wykonywaniu (komendy [Compute] czy [Eval] są dość
    kiepskie).

    Mechanizm ekstrakcji to coś, co nas z tej nędzy trochę ratuje: daje
    on nam możliwość przetłumaczenia naszego programu w Coqu na program
    w jakimś nieco bardziej mainstreamowym języku funkcyjnym (jak OCaml,
    Haskell czy Scheme), w których programy da się normalnie odpalać i
    działają nawet szybko.

    Mechanizm ten nie będzie nas interesował, ponieważ moim zdaniem jest
    on ślepą uliczką ewolucji - zamiast niego trzeba będzie po prostu
    wymyślić sposób efektywnej kompilacji Coqowych programow, ale to już
    temat na inną bajkę.

    Nie będziemy zatem zbytnio zagłębiać się w szczegóły ekstrakcji -
    zanim zupełnie o niej zapomnimy, zobaczmy tylko jeden przykład. *)

Extraction Language Haskell.

(** Komenda [Extraction Language] ustawia język, do którego chcemy
    ekstrahować. My użyjemy Haskella, gdyż pozostałych dostępnych
    języków nie lubię. *)

Extraction again.div'.
(* ===> div' :: Nat -> Nat -> Nat
        div' = div'_aux *)

(** Komenda [Extraction p] tłumaczy Coqowy program [p] na program
    Haskellowy. Mimo że nie znamy Haskella, spróbujmy przeczytać
    wynikowy program.

    Wynikiem ekstrakcji jest Haskellowa funkcja [div'] o typie
    [Nat -> Nat -> Nat], gdzie [Nat] to Haskellowa wersja Coqowego [nat]
    (podwójny dwukropek [::] oznacza w Haskellu to samo, co pojedynczy
    dwukropek [:] w Coqu). Funkcja [div'] jest zdefiniowana jako... i tu
    zaskoczenie... [div'_aux]. Ale jak to? Rzućmy jeszcze raz okiem na
    oryginalną, Coqową definicję. *)

Print again.div'.
(* ===> again.div' = 
        fun n m : nat => again.div'_aux (again.divD_all n m)
             : nat -> nat -> nat *)

(** Gdzież w wyekstrahowanym programie podział się dowód [divD_all n m]?
    Otóż nie ma go, bo Haskell to zwykły język programowania, w którym
    nie można dowodzić. O to właśnie chodzi w mechanizmie ekstrakcji -
    w procesie ekstrakcji wyrzucić z Coqowego programu wszystkie dowody
    i przetłumaczyć tylko tę część programu, która jest niezbędna, by
    wyekstrahowany program się obliczał.

    Mogłoby się wydawać dziwne, że najpierw w pocie czoła dowodzimy czegoś
    w Coqu, a potem mechanizm ekstrakcji się tego pozbywa. Jest to jednak
    całkiem naturalne - skoro udało nam się udowodnić jakąś właściwość
    naszego programu, to wiemy, że ma on tę właściwość i dowód nie jest
    nam już do niczego potrzebny, a zatem ekstrakcja może się go pozbyć. *)

Print again.div'_aux.
(* ===>
    again.div'_aux = 
    fix div'_aux (n m : nat) (d : again.divD n m) {struct d} : nat :=
    match le_lt_dec (S m) n with
    | left H =>
        S (div'_aux (n - S m) m (again.divD_ge_inv n m H d))
    | right _ => 0
    end
      : forall n m : nat, again.divD n m -> nat *)

Extraction again.div'_aux.
(* ===>
    div'_aux :: Nat -> Nat -> Nat
    div'_aux n m =
      case le_lt_dec (S m) n of {
       Left -> S (div'_aux (sub n (S m)) m);
       Right -> O} *)

(** A tak wygląda wyekstrahowana funkcja [div'_aux]. Jeżeli pominiemy
    różnice składniowe między Coqiem i Haskellem (w Coqu typ jest na
    dole, po dwukropku, a w Haskellu na górze, przed definicją; w Coqu
    mamy [match], a w Haskellu [case] etc.) to wygląda całkiem podobnie.
    Kluczową różnicą jest widniejący w Coqowej wersji dowód należenia do
    dziedziny [again.divD_ge_inv n m H d], który w Haskellowym ekstrakcie
    został usunięty.

    Cały ten cyrk z przerabianiem [divD] na prawdziwy predykat był po
    to, żeby dowód należenia do dziedziny mógł zostać usunięty podczas
    ekstrakcji. Dzięki temu wyekstrahowany program w Haskellu wygląda
    jak gdyby został napisany ręcznie. Jest też szybszy i krótszy, bo
    nie ma tam wzmianki o [divD_all], która musiałaby się pojawić, gdyby
    [divD] było rodziną typów, a nie predykatem. *)

Extraction div'_aux.
(* ===> 
    div'_aux :: Nat -> Nat -> DivD -> Nat
    div'_aux _ _ h =
      case h of {
       DivD_lt _ _ -> O;
       DivD_ge n m h' -> S (div'_aux (sub n (S m)) m h')} *)

(** Tak wygląda ekstrakt oryginalnego [div'_aux], tzn. tego, w którym [divD]
    nie jest predykatem, lecz rodziną typów. W wyekstrahowanym programie, w
    typie funkcji [div'_aux] pojawia się złowieszczy typ [DivD], który jest
    zupełnie zbędny, bo Haskell (i żaden inny funkcyjny język programowania,
    który nie jest przeznaczony do dowodzenia) nie narzuca żadnych ograniczeń
    na wywołania rekurencyjne.

    No, to by było na tyle. Życzę ci, żebyś nigdy nie musiał stosować
    wariantu metody induktywnej dziedziny opisanej w tym podrozdziale
    ani nie musiał niczego ekstrahować. *)

(** * Plugin [Equations] *)

(** **** Ćwiczenie *)

(** Zainstaluj plugin
    #<a class='link' href='https://github.com/mattam82/Coq-Equations'>Equations</a>#.
    Przeczytaj
    #<a class='link' href='https://raw.githubusercontent.com/mattam82/Coq-Equations/master/doc/equations_intro.v'>
    tutorial</a>#.

    Następnie znajdź jakiś swój dowód przez indukcję, który był skomplikowany
    i napisz prostszy dowód za pomocą komendy [Equations] i taktyki [funelim].
*)

(** * Podsumowanie (TODO) *)

(** Póki co nie jest źle, wszakże udało nam się odkryć indukcję wykresową,
    czyli metodę dowodzenia właściwości funkcji za pomocą specjalnie do
    niej dostosowanej reguły indukcji, wywodzącej się od reguły indukcji
    jej wykresu. *)