(** * D2j: Indukcja wykresowa *)

Require Import List.
Import ListNotations.

Require Import Arith Lia.

From Typonomikon Require Import D5.
From Typonomikon Require Export D2h.

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
    da się obliczyć lub nikt nie potrafi pokazać, że terminują (takie
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

(** * Podsumowanie (TODO) *)

(** Póki co nie jest źle, wszakże udało nam się odkryć indukcję wykresową,
    czyli metodę dowodzenia właściwości funkcji za pomocą specjalnie do
    niej dostosowanej reguły indukcji, wywodzącej się od reguły indukcji
    jej wykresu. *)