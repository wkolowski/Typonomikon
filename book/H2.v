(** * H2: Funkcje *)

Require Import Arith.

(* begin hide *)
Require Import Recdef.

(** Prerekwizyty:
    - [Empty_set], [unit], [prod], [sum] i funkcje
    - właściwości konstruktorów?
    - [exists!]
    - równość [eq] *)

(*
TODO: Zadanie z dwiema dziwnymi identycznościami
*)

(* end hide *)

(** W tym rozdziale zapoznamy się z najważniejszymi rodzajami funkcji.
    Trzeba przyznać na wstępie, że rozdział będzie raczej matematyczny
    (co wcale nie powinno cię odstraszać - matematyka jest świetna, a
    najbardziej praktyczną rzeczą w kosmosie jest dobra teoria). *)

(** * Funkcje *)

(** Potrafisz już posługiwać się funkcjami. Mimo tego zróbmy krótkie
    przypomnienie.

    Typ funkcji (niezależnych) z [A] w [B] oznaczamy przez [A -> B]. W
    Coqu funkcje możemy konstruować za pomocą abstrakcji (np. [fun n :
    nat => n + n]) albo za pomocą rekursji strukturalnej. Eliminować zaś
    możemy je za pomocą aplikacji: jeżeli [f : A -> B] oraz [x : A], to
    [f x : B].

    Funkcje wyrażają ideę przyporządkowania: każdemu elementowi dziedziny
    funkcja przyporządkowuje element przeciwdziedziny. Jednak status
    dziedziny i przeciwdziedziny nie jest taki sam: każdemu elementowi
    dziedziny coś odpowiada, jednak mogą istnieć elementy przeciwdziedziny,
    które nie są obrazem żadnego elementu dziedziny.

    Co więcej, w Coqu wszystkie funkcje są konstruktywne, tzn. mogą zostać
    obliczone. Jest to coś, co bardzo mocno odróżnia Coqa oraz rachunek
    konstrukcji (jego teoretyczną podstawę) od innych systemów formalnych. *)

Notation "f $ x" := (f x) (left associativity, at level 110, only parsing).
Notation "x |> f" := (f x) (right associativity, at level 60, only parsing).

Check plus (2 + 2) (3 + 3).
Check plus $ 2 + 2 $ 3 + 3.

Check (fun n : nat => n + n) 21.
Check 21 |> fun n : nat => n + n.

(** Najważniejszą rzeczą, jaką możemy zrobić z funkcją, jest zaaplikowanie
    jej do argumentu. Jest to tak częsta operacja, że zdefiniujemy sobie
    dwie notacje, które pozwolą nam zaoszczędzić kilka stuknięć w klawiaturę.

    Notacja [$] (pożyczona z języka Haskell) będzie nam służyć do niepisania
    nawiasów: jeżeli argumentami funkcji będą skomplikowane termy, zamiast
    pisać wokół nich parę nawiasów, będziemy mogli wstawić tylko jeden symbol
    dolara "$$". Dzięki temu zamiast 2n nawiasów napiszemy tylko n znaków "$$"
    (choć trzeba przyznać, że będziemy musieli pisać więcej spacji).

    Notacja [|>] (pożyczona z języka F##) umożliwi nam pisanie aplikacji w odwrotnej
    kolejności. Dzięki temu będziemy mogli np. pomijać nawiasy w abstrakcji. Jako,
    że nie da się zrobić notacji w stylu "x f", jest to najlepsze dostępne nam
    rozwiązanie. *)

Definition comp
  {A B C : Type} (f : A -> B) (g : B -> C) : A -> C :=
    fun x : A => g (f x).

Notation "f .> g" := (comp f g) (left associativity, at level 40).

(** Drugą najważniejszą operacją, jaką możemy wykonywać na funkcjach, jest
    składanie. Jedynym warunkiem jest aby przeciwdziedzina pierwszej funkcji
    była taka sama, jak dziedzina drugiej funkcji. *)

Lemma comp_assoc :
  forall (A B C D : Type) (f : A -> B) (g : B -> C) (h : C -> D),
    (f .> g) .> h = f .> (g .> h).
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

(** Składanie funkcji jest łączne. Zagadka: czy jest przemienne?

    Uwaga techniczna: jeżeli prezentuję jakieś twierdzenie bez dowodu, to
    znaczy, że dowód jest ćwiczeniem. *)

Definition id {A : Type} : A -> A := fun x : A => x.

(** Najważniejszą funkcją w całym kosmosie jest identyczność. Jest to funkcja,
    która nie robi zupełnie nic. Jej waga jest w tym, że jest ona elementem
    neutralnym składania funkcji. *)

Lemma id_left :
  forall (A B : Type) (f : A -> B), id .> f = f.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Lemma id_right :
  forall (A B : Type) (f : A -> B), f .> id = f.
(* begin hide *)
Proof. reflexivity. Qed.
(* end hide *)

Definition const {A B : Type} (b : B) : A -> B := fun _ => b.

(** Funkcja stała to funkcja, która ignoruje swój drugi argument i zawsze
    zwraca pierwszy argument. *)

Definition flip
  {A B C : Type} (f : A -> B -> C) : B -> A -> C :=
    fun (b : B) (a : A) => f a b.

(** [flip] to całkiem przydatny kombinator (funkcja wyższego rzędu), który
    zamienia miejscami argumenty funkcji dwuargumentowej. *)

Fixpoint iter {A : Type} (n : nat) (f : A -> A) : A -> A :=
match n with
    | 0 => id
    | S n' => f .> iter n' f
end.

(** Ostatnim przydatnim kombinatorem jest [iter]. Służy on do składania
    funkcji samej ze sobą [n] razy. Oczywiście funkcja, aby można ją było
    złożyć ze sobą, musi mieć identyczną dziedzinę i przeciwdziedzinę. *)

(** * Aksjomat ekstensjonalności *)

(** Ważną kwestią jest ustalenie, kiedy dwie funkcje są równe. Zacznijmy od
    tego, że istnieją dwie koncepcje równości:
    - intensjonalna — funkcje są zdefiniowane przez identyczne (czyli
      konwertowalne) wyrażenia
    - ekstensjonalna — wartości funkcji dla każdego argumentu są równe *)

Print eq.
(* ===>
    Inductive eq (A : Type) (x : A) : A -> Prop :=
        | eq_refl : x = x
*)

(** Podstawowym i domyślnym rodzajem równości w Coqu jest równość
    intensjonalna, której właściwości już znasz. Każda funkcja, na mocy
    konstruktora [eq_refl], jest równa samej sobie. Prawdą jest też mniej
    oczywisty fakt: każda funkcja jest równa swojej η-ekspansji. *)

Lemma eta_expansion :
  forall (A B : Type) (f : A -> B), f = fun x : A => f x.
Proof. reflexivity. Qed.

Print Assumptions eta_expansion.
(* ===> Closed under the global context *)

(** η-ekspansja funkcji [f] to nic innego, jak funkcja anonimowa, która
    bierze [x] i zwraca [f x]. Nazwa pochodzi od greckiej litery η (eta).
    Powyższe twierdzenie jest trywialne, gdyż równość zachodzi na mocy
    konwersji.

    Warto podkreślić, że jego prawdziwość nie zależy od żadnych aksjomatów.
    Stwierdzenie to możemy zweryfikować za pomocą komendy [Print Assumptions],
    która wyświetla listę aksjomatów, które zostały wykorzystane w definicji
    danego termu. Napis "Closed under the global context" oznacza, że żadnego
    aksjomatu nie użyto. *)

Lemma plus_1_eq :
  (fun n : nat => 1 + n) = (fun n : nat => n + 1).
Proof.
  trivial.
  Fail rewrite plus_comm. (* No i co teraz? *)
Abort.

(** Równość intensjonalna ma jednak swoje wady. Główną z nich jest to, że
    jest ona bardzo restrykcyjna. Widać to dobrze na powyższym przykładzie:
    nie jesteśmy w stanie udowodnić, że funkcje [fun n : nat => 1 + n] oraz
    [fun n : nat => n + 1] są równe, gdyż zostały zdefiniowane za pomocą
    innych termów. Mimo, że termy te są równe, to nie są konwertowalne, a
    zatem funkcje też nie są konwertowalne. Nie znaczy to jednak, że nie są
    równe — po prostu nie jesteśmy w stanie w żaden sposób pokazać, że są. *)

Require Import FunctionalExtensionality.

Check @functional_extensionality.
(* ===> @functional_extensionality
          : forall (A B : Type) (f g : A -> B),
              (forall x : A, f x = g x) -> f = g *)

(** Z tarapatów wybawić nas może jedynie aksjomat ekstensjonalności dla
    funkcji, zwany w Coqu [functional_extensionality] (dla funkcji, które
    nie są zależne) lub [functional_extensionality_dep] (dla funkcji
    zależnych).

    Aksjomat ten głosi, że [f] i [g] są równe, jeżeli są równe dla wszystkich
    argumentów. Jest on bardzo użyteczny, a przy tym nie ma żadnych smutnych
    konsekwencji i jest kompatybilny z wieloma innymi aksjomatami. Z tych
    właśnie powodów jest on jednym z najczęściej używanych w Coqu aksjomatów.
    My też będziemy go wykorzystywać. *)

Lemma plus_1_eq :
  (fun n : nat => 1 + n) = (fun n : nat => n + 1).
Proof.
  extensionality n. rewrite plus_comm. trivial.
Qed.

(** Sposób użycia aksjomatu jest banalnie prosty. Jeżeli mamy cel postaci
    [f = g], to taktyka [extensionality x] przekształca go w cel postaci
    [f x = g x], o ile tylko nazwa [x] nie jest już wykorzystana na coś
    innego.

    Dzięki zastosowaniu aksjomatu nie musimy już polegać na konwertowalności
    termów definiujących funkcje. Wystarczy udowodnić, że są one równe. W
    tym przypadku robimy to za pomocą twierdzenia [plus_comm]. *)

(** **** Ćwiczenie *)

(** Użyj aksjomatu ekstensjonalności, żeby pokazać, że dwie funkcje binarne
    są równe wtedy i tylko wtedy, gdy ich wartości dla wszystkich argumentów
    są równe. *)

Lemma binary_funext :
  forall (A B C : Type) (f g : A -> B -> C),
    f = g <-> forall (a : A) (b : B), f a b = g a b.
(* begin hide *)
Proof.
  split; intros.
    subst. trivial.
    extensionality a. extensionality b. apply H.
Qed.
(* end hide *)

(** * Odwrotności i izomorfizmy (TODO) *)

(** W tym podrozdziale zajmiemy się pojęciem funkcji odwrotnej i płynącą z
    niego mądrością. *)

Definition has_preinverse {A B : Type} (f : A -> B) : Type :=
  {g : B -> A | forall b : B, f (g b) = b}.

Definition has_postinverse {A B : Type} (f : A -> B) : Type :=
  {g : B -> A | forall a : A, g (f a) = a}.

(** Intuicja jest dość prosta: wiemy ze szkoły, że na liczbach całkowitych
    odejmowanie jest odwrotnością dodawania (np. a + b - b = a), tzn. jeżeli
    do a dodamy b, a potem odejmiemy b, to znowu mamy a. Podobnie w liczbach
    rzeczywistych mnożenie przez liczbę niezerową ma odwrotność w postaci
    dzielenia, np. (x * y) / y = x.

    Oczywiście pojęcie odwrotności dotyczy nie tylko działań na liczbach,
    ale także dowolnych funkcji - [g] jest odwrotnością [f], gdy odwraca
    ono działanie [f] dla dowolnego argumentu [a], tzn. najpierw mamy [a],
    potem aplikujemy [f] i mamy [f a], zaś na koniec aplikujemy [g] i znów
    mamy [a], czyli [g (f a) = a]. To właśnie jest napisane w definicji
    [has_postinverse].

    No właśnie - powyższy opis jest opisem postodwrotności. Nazwa wynika z
    kolejności - [g] jest postodwrotnością [f], gdy najpierw aplikujemy [f],
    a potem odwracamy jego działanie za pomocą [g] (po łacinie "post" znaczy
    "po", np. "post meridiem" znaczy "po południu").

    Analogicznie, choć może nieco mniej intuicyjnie, prezentuje się definicja
    preodwrotności (po łacinie "prae" znaczy "przed"). [g] jest preodwrotnością
    [f], gdy [f] jest postodwrotnością [g]. Innymi słowy: [f] ma preodwrotność,
    jeżeli odwraca ono działanie jakiejś funkcji.

    Dobra, wystarczy gadania. Czas na ćwiczenia. *)

(** **** Ćwiczenie *)

(** Pokaż, że odjęcie [n] jest postodwrotnością dodania [n]. Czy jest także
    preodwrotnością? *)

Lemma plus_n_has_postinverse_sub_n :
  forall n : nat,
    has_postinverse (plus n).
(* begin hide *)
Proof.
  intro. red.
  exists (fun m : nat => minus m n).
  induction n as [| n'];  cbn; intro m.
    rewrite <- minus_n_O. reflexivity.
    apply IHn'.
Defined.
(* end hide *)

(* begin hide *)
Lemma plus_0_has_preinverse :
  has_preinverse (plus 0).
Proof.
  red. exists id. cbn. reflexivity.
Defined.

Lemma plus_S_has_no_preinverse :
  forall n : nat,
    has_preinverse (plus (S n)) -> False.
Proof.
  intros n [f eq]. specialize (eq 0). inversion eq.
Qed.
(* end hide *)

(** Zauważ, że sortem [has_preinverse] i [has_postinverse] jest [Type], nie
    zaś [Prop]. Jest tak dlatego, że o ile stwierdzenie "f jest pre/post
    odwrotnością g" jest zdaniem, to posiadanie odwrotności już nie, gdyż
    dana funkcja może mieć wiele różnych odwrotności. *)

(** **** Ćwiczenie *)

(** Rozważmy funkcję [app [1; 2; 3]], która dokleja na początek listy liczb
    naturalnych listę [[1; 2; 3]]. Znajdź dwie różne jej postodwrotności (nie
    musisz formalnie dowodzić, że są różne - wystarczy nieformalny argument).
    Czy funkcja ta ma preodwrotność? *)

Require Import D5.

(* begin hide *)
Goal has_postinverse (app [1; 2; 3]).
Proof.
  red. exists (drop 3). cbn. intro. rewrite drop_0. reflexivity.
Qed.

Goal has_postinverse (app [1; 2; 3]).
Proof.
  red.
  exists (
    fun l : list nat =>
    match l with
        | [] => []
        | [_] => []
        | [x; y] => [y; x]
        | _ :: _ :: _ :: t => t
    end).
  cbn. reflexivity.
Qed.

(** Widać na oko, że obie odwrotności są różne. Funkcja oczywiście nie ma
    preodwrotności. *)

Goal has_preinverse (app [1; 2; 3]) -> False.
Proof.
  intros [f eq]. specialize (eq []). inversion eq.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Czasem funkcja może mieć naprawdę dużo odwrotności. Pokaż, że funkcja
    [cons x] dla [x : A] ma ich nieskończenie wiele. Nie musisz dowodzić,
    że odwrotności są różne (ani że jest ich dużo), jeżeli widać to na
    pierwszy rzut oka. *)

(* begin hide *)
Definition anticons {A : Type} (n : nat) (x : A) (l : list A) : list A :=
match l with
    | [] => replicate n x
    | _ :: t => t
end.

Lemma cons_has_lots_of_postinverses :
  forall (A : Type) (n : nat) (x : A),
    has_postinverse (cons x).
Proof.
  intros. red. exists (anticons n x). cbn. reflexivity.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Dla listowych funkcji widzieliśmy postodwrotności, ale nie widzieliśmy
    preodwrotności. Może więc preodwrotności nie istnieją? Otóż nie tym
    razem!

    Dla jakich [n] funkcja [cycle n] ma (pre/post)odwrotność?  *)

Definition uncycle {A : Type} (n : nat) (l : list A) : list A :=
  cycle (length l - n) l.

Lemma cycle_has_preinverse :
  forall (A : Type) (n : nat),
    has_preinverse (@cycle A n).
Proof.
  intros. red.
  exists (uncycle n).
  unfold uncycle, cycle.
Abort.

(*
Lemma cycle'_has_preinverse :
  forall (A : Type) (n : nat),
    has_preinverse (@cycle' A n).
Proof.
  intros. red.
  exists (fun l : list A => cycle' (length l - n) l).
  induction n as [| n']; cbn.
Abort.
*)
(* end hide *)

Definition isomorphism {A B : Type} (f : A -> B) : Type :=
  {g : B -> A | (forall a : A, g (f a) = a) /\
                (forall b : B, f (g b) = b)}.

Lemma iso_has_preinverse :
  forall {A B : Type} {f : A -> B},
    isomorphism f -> has_preinverse f.
(* begin hide *)
Proof.
  destruct 1 as (g & Hpre & Hpost).
  red. exists g. assumption.
Qed.
(* end hide *)

Lemma iso_has_postinverse :
  forall {A B : Type} {f : A -> B},
    isomorphism f -> has_postinverse f.
(* begin hide *)
Proof.
  destruct 1 as (g & Hpre & Hpost).
  red. exists g. assumption.
Qed.
(* end hide *)

Lemma both_inverses_isomorphism :
  forall {A B : Type} {f : A -> B},
    has_preinverse f -> has_postinverse f -> isomorphism f.
(* begin hide *)
Proof.
  destruct 1 as (g1 & Hpre), 1 as (g2 & Hpost).
  red. exists (g1 .> f .> g2). split; intros.
    unfold comp. rewrite Hpre, Hpost. reflexivity.
    unfold comp. rewrite Hpost, Hpre. reflexivity.
Qed.
(* end hide *)

(** * Skracalność (TODO) *)

Definition precancellable {A B : Type} (f : A -> B) : Prop :=
  forall (X : Type) (g h : B -> X), f .> g = f .> h -> g = h.

Definition postcancellable {A B : Type} (f : A -> B) : Prop :=
  forall (X : Type) (g h : X -> A), g .> f = h .> f -> g = h.

Lemma has_preinverse_precancellable :
  forall {A B : Type} {f : A -> B},
    has_preinverse f -> precancellable f.
(* begin hide *)
Proof. (* TODO: has_preinverse_precancellable *)
Admitted.
(* end hide *)

Lemma has_postinverse_postcancellable :
  forall {A B : Type} {f : A -> B},
    has_postinverse f -> postcancellable f.
(* begin hide *)
Proof.
Admitted.
(* end hide *)

(** * Injekcje *)

Definition injective {A B : Type} (f : A -> B) : Prop :=
  forall x x' : A, f x = f x' -> x = x'.

(** Objaśnienia zacznijmy od nazwy. Po łacinie "iacere" znaczy "rzucać",
    zaś "in" znaczy "w, do". W językach romańskich samo słowo "injekcja"
    oznacza zaś zastrzyk. Bliższym matematycznemu znaczeniu byłoby jednak
    tłumaczenie "wstrzyknięcie". Jeżeli funkcja jest injekcją, to możemy
    też powiedzieć, że jest "injektywna". Inną nazwą jest "funkcja
    różnowartościowa". Na wiki można zapoznać się z obrazkami poglądowymi:

    https://en.wikipedia.org/wiki/Bijection,%%20injection%%20and%%20surjection

    Podstawowa idea jest prosta: jeżeli funkcja jest injekcją, to identyczne
    jej wartości pochodzą od równych argumentów.

    Przekonajmy się na przykładzie. *)

Goal injective (fun n : nat => 2 + n).
Proof.
  unfold injective; intros. destruct x, x'; cbn in *.
    trivial.
    inversion H.
    inversion H.
    inversion H. trivial.
Qed.

(** Funkcja [fun n : nat => 2 + n], czyli dodanie [2] z lewej strony, jest
    injekcją, gdyż jeżeli [2 + n = 2 + n'], to rozwiązując równanie dostajemy
    [n = n']. Jeżeli wartości funkcji są równe, to argumenty również muszą
    być równe.

    Zobaczmy też kontrprzykład. *)

Goal ~ injective (fun n : nat => n * n - n).
Proof.
  unfold injective, not; intros.
  specialize (H 0 1). cbn in H. specialize (H eq_refl). inversion H.
Qed.

(** Funkcja f(n) = n^2 - n nie jest injekcją, gdyż mamy zarówno f(0) = 0
    jak i f(1) = 0. Innymi słowy: są dwa nierówne argumenty (0 i 1), dla
    których wartość funkcji jest taka sama (0).

    A oto alternatywna definicja. *)

Definition injective' {A B : Type} (f : A -> B) : Prop :=
  forall x x' : A, x <> x' -> f x <> f x'.

(** Głosi ona, że funkcja injektywna to funkcja, która dla różnych argumentów
    przyjmuje różne wartości. Innymi słowy, injekcja to funkcja, która
    zachowuje relację [<>]. Przykład 1 możemy sparafrazować następująco:
    jeżeli [n] jest różn od [n'], to wtedy [2 + n] jest różne od [2 + n'].

    Definicja ta jest równoważna poprzedniej, ale tylko pod warunkiem, że
    przyjmiemy logikę klasyczną. W logice konstruktywnej pierwsza definicja
    jest lepsza od drugiej. *)

(** **** Ćwiczenie *)

(** Pokaż, że [injective] jest mocniejsze od [injective']. Pokaż też, że w
    logice klasycznej są one równoważne. *)

Lemma injective_injective' :
  forall (A B : Type) (f : A -> B),
    injective f -> injective' f.
(* begin hide *)
Proof.
  unfold injective, injective', not; intros.
  apply H0. apply H. assumption.
Qed.
(* end hide *)

Lemma injective'_injective :
  (forall P : Prop, ~ ~ P -> P) ->
  forall (A B : Type) (f : A -> B),
    injective' f -> injective f.
(* begin hide *)
Proof.
  unfold injective, injective', not; intros.
  apply H. intro. apply (H0 x x'); assumption.
Qed.
(* end hide *)

(** Udowodnij, że różne funkcje są lub nie są injektywne. *)

Lemma id_injective :
  forall A : Type, injective (@id A).
(* begin hide *)
Proof.
  intro. unfold injective, id. trivial.
Qed.
(* end hide *)

Lemma S_injective : injective S.
(* begin hide *)
Proof.
  red. inversion 1. trivial.
Qed.
(* end hide *)

Lemma const_unit_inj :
  forall (A : Type) (a : A),
    injective (fun _ : unit => a).
(* begin hide *)
Proof.
  unfold injective; intros. destruct x, x'. trivial.
Qed.
(* end hide *)

Lemma add_k_left_inj :
  forall k : nat, injective (fun n : nat => k + n).
(* begin hide *)
Proof.
  red. induction k as [| k']; cbn; intros.
    assumption.
    inversion H. apply IHk'. assumption.
Qed.
(* end hide *)

Lemma mul_k_inj :
  forall k : nat, k <> 0 -> injective (fun n : nat => k * n).
(* begin hide *)
Proof.
  red. intros k H x x'. generalize dependent k. generalize dependent x'.
  induction x as [| y]; induction x' as [| y']; cbn; intros.
    trivial.
    do 2 (rewrite mult_comm in H0; cbn in *). destruct k.
      contradiction H. trivial.
      cbn in H0. inversion H0.
    rewrite mult_0_r in H0. rewrite mult_comm in H0. cbn in H0. destruct k.
      contradiction H. trivial.
      cbn in H0. inversion H0.
    f_equal. apply (IHy y' k).
      assumption.
      SearchPattern (_ * S _ = _).
      do 2 rewrite mult_succ_r in H0. rewrite plus_comm in H0 at 1.
        replace (k * y' + k) with (k + k * y') in H0.
          assert (Hinj : injective (fun n : nat => k + n)).
            apply add_k_left_inj.
          red in Hinj. apply Hinj in H0. assumption.
        apply plus_comm.
Qed.
(* end hide *)

Lemma const_2elem_not_inj :
  forall (A B : Type) (b : B),
    (exists a a' : A, a <> a') -> ~ injective (fun _ : A => b).
(* begin hide *)
Proof.
  unfold injective, not; intros. destruct H as [a [a' H]].
  specialize (H0 a a' eq_refl). contradiction.
Qed.
(* end hide *)

Lemma mul_k_0_not_inj :
  ~ injective (fun n : nat => 0 * n).
(* begin hide *)
Proof.
  cbn. apply const_2elem_not_inj. exists 0, 1. inversion 1.
Qed.
(* end hide *)

Lemma pred_not_injective : ~ injective pred.
(* begin hide *)
Proof.
  unfold injective; intro. specialize (H 0 1 eq_refl). inversion H.
Qed.
(* end hide *)

(** Jedną z ważnych właściwości injekcji jest to, że są składalne:
    złożenie dwóch injekcji daje injekcję. *)

Lemma inj_comp :
  forall (A B C : Type) (f : A -> B) (g : B -> C),
    injective f -> injective g -> injective (f .> g).
(* begin hide *)
Proof.
  unfold injective, comp; intros.
  apply H, H0. assumption.
Qed.
(* end hide *)

(** Ta właściwość jest dziwna. Być może kiedyś wymyślę dla niej jakąś
    bajkę. *)

Lemma LOLWUT :
  forall (A B C : Type) (f : A -> B) (g : B -> C),
    injective (f .> g) -> injective f.
(* begin hide *)
Proof.
  unfold injective, comp; intros.
  apply H. rewrite H0. trivial.
Qed.
(* end hide *)

(** Na zakończenie należy dodać do naszej interpretacji pojęcia "injekcja"
    jeszcze jedną ideę. Mianowicie jeżeli istnieje injekcja [f : A -> B],
    to ilość elementów typu [A] jest mniejsza lub równa liczbie elementów
    typu [B], a więc typ [A] jest w pewien sposób mniejszy od [B].

    [f] musi przyporządkować każdemu elementowi [A] jakiś element [B]. Gdy
    elementów [A] jest więcej niż [B], to z konieczności któryś z elementów
    [B] będzie obrazem dwóch lub więcej elementów [A].

    Wobec powyższego stwierdzenie "złożenie injekcji jest injekcją" możemy
    zinterpretować po prostu jako stwierdzenie, że relacja porządku, jaką
    jest istnienie injekcji, jest przechodnia. (TODO: to wymagałoby relacji
    jako prerekwizytu). *)

(** **** Ćwiczenie *)

(** Udowodnij, że nie istnieje injekcja z [bool] w [unit]. Znaczy to, że
    [bool] ma więcej elementów, czyli jest większy, niż [unit]. *)

Lemma no_inj_bool_unit :
  ~ exists f : bool -> unit, injective f.
(* begin hide *)
Proof.
  unfold not, injective; intros. destruct H as [f H].
  specialize (H true false). destruct (f true), (f false).
  specialize (H eq_refl). inversion H.
Qed.
(* end hide *)

(** Pokaż, że istnieje injekcja z typu pustego w każdy inny. Znaczy to,
    że [Empty_set] ma nie więcej elementów, niż każdy inny typ (co nie
    powinno nas dziwić, gdyż [Empty_set] nie ma żadnych elementów). *)

Lemma inj_Empty_set_A :
  forall A : Type, exists f : Empty_set -> A, injective f.
(* begin hide *)
Proof.
  intro. exists (fun e : Empty_set => match e with end).
  red. inversion x.
Qed.
(* end hide *)


(** * Surjekcje *)

(** Drugim ważnym rodzajem funkcji są surjekcje. *)

Definition surjective {A B : Type} (f : A -> B) : Prop :=
    forall b : B, exists a : A, f a = b.

(** I znów zacznijmy od nazwy. Po francusku "sur" znaczy "na", zaś słowo
    "iacere" już znamy (po łac. "rzucać"). Słowo "surjekcja" moglibyśmy
    więc przetłumaczyć jako "pokrycie". Tym bowiem w istocie jest surjekcja
    — jest to funkcja, która "pokrywa" całą swoją przeciwdziedzinę.

    Owo "pokrywanie" w definicji wyraziliśmy w ten sposób: dla każdego
    elementu [b] przeciwdziedziny [B] istnieje taki element [a] dziedziny
    [A], że [f a = b].

    Zobaczmy przykład i kontrprzykład. *)

Lemma pred_surjective : surjective pred.
Proof.
  unfold surjective; intros. exists (S b). cbn. trivial.
Qed.

(** Powyższe twierdzenie głosi, że "funkcja [pred] jest surjekcją", czyli,
    parafrazując, "każda liczba naturalna jest poprzednikiem innej liczby
    naturalnej". Nie powinno nas to zaskakiwać, wszakże każda liczba naturalna
    jest poprzednikiem swojego następnika, tzn. [pred (S n) = n]. *)

Lemma S_not_surjective : ~ surjective S.
Proof.
  unfold surjective; intro. destruct (H 0). inversion H0.
Qed.

(** Surjekcją nie jest za to konstruktor [S]. To również nie powinno nas
    dziwić: istnieje przecież liczba naturalna, która nie jest następnikiem
    żadnej innej. Jest nią oczywiście zero.

    Surjekcje cieszą się właściwościami podobnymi do tych, jakie są udziałem
    injekcji. *)

(** **** Ćwiczenie *)

(** Pokaż, że złożenie surjekcji jest surjekcją. Udowodnij też "dziwną
    właściwość" surjekcji. *)

Lemma sur_comp :
  forall (A B C : Type) (f : A -> B) (g : B -> C),
    surjective f -> surjective g -> surjective (f .> g).
(* begin hide *)
Proof.
  unfold surjective, comp; intros A B C f g Hf Hg c.
  destruct (Hg c) as [b Heq]. destruct (Hf b) as [a Heq'].
  subst. exists a. trivial.
Qed.
(* end hide *)

Lemma LOLWUT_sur :
  forall (A B C : Type) (f : A -> B) (g : B -> C),
    surjective (f .> g) -> surjective g.
(* begin hide *)
Proof.
  unfold surjective, comp.
  intros A B C f g Hgf c.
  destruct (Hgf c) as [a Heq].
  exists (f a). assumption.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Zbadaj, czy wymienione funkcje są surjekcjami. Sformułuj i udowodnij
    odpowiednie twierdzenia.

    Funkcje: identyczność, dodawanie (rozważ zero osobno), odejmowanie,
    mnożenie (rozważ 1 osobno). *)

(* begin hide *)
Lemma id_sur :
  forall A : Type, surjective (@id A).
Proof.
  red; intros. exists b. trivial.
Qed.

Lemma plus_0_l_sur : surjective (fun n : nat => 0 + n).
Proof.
  red; intros. exists b. trivial.
Qed.

Lemma plus_0_r_sur : surjective (fun n : nat => n + 0).
Proof.
  red; intros. exists b. rewrite <- plus_n_O. trivial.
Qed.

Lemma plus_Sn_l_not_sur :
  forall k : nat, ~ surjective (fun n : nat => S k + n).
Proof.
  unfold surjective, not; intros. specialize (H 0).
  destruct H as [a H]. inversion H.
Qed.

Lemma plus_Sn_r_not_sur :
  forall k : nat, ~ surjective (fun n : nat => n + S k).
Proof.
  unfold surjective, not; intros. specialize (H 0).
  destruct H as [a H]. rewrite plus_comm in H. inversion H.
Qed.

Lemma minus_sur :
  forall k : nat, surjective (fun n : nat => n - k).
Proof.
  red; intros. exists (k + b). rewrite minus_plus. trivial.
Qed.

Lemma mult_1_l_sur : surjective (fun n : nat => 1 * n).
Proof.
  red; intros. exists b. Search (1 * _). apply Nat.mul_1_l.
Qed.

Lemma mult_1_r_sur : surjective (fun n : nat => n * 1).
Proof.
  red; intros. exists b. apply Nat.mul_1_r.
Qed.

Lemma mult_0_l_not_sur : ~ surjective (fun n : nat => 0 * n).
Proof.
  unfold surjective, not; intros. specialize (H 1).
  destruct H as [a H]. cbn in H. inversion H.
Qed.

Lemma mult_0_r_not_sur : ~ surjective (fun n : nat => n * 0).
Proof.
  unfold surjective, not; intros. specialize (H 1).
  destruct H as [a H]. rewrite Nat.mul_0_r in H. inversion H.
Qed.

Lemma mult_SS_l_not_sur :
  forall k : nat, ~ surjective (fun n : nat => S (S k) * n).
Proof.
  unfold surjective, not; intros. specialize (H 1).
  destruct H as [a H]. destruct a as [| a']; cbn in H.
    rewrite Nat.mul_0_r in H. inversion H.
    inversion H. rewrite plus_comm in H1. inversion H1.
Qed.

Lemma mult_SS_r_not_sur :
  forall k : nat, ~ surjective (fun n : nat => n * S (S k)).
Proof.
  unfold surjective, not; intros. specialize (H 1).
  destruct H as [a H]. destruct a as [| a']; inversion H.
Qed.
(* end hide *)

(** Tak jak istnienie injekcji [f : A -> B] oznacza, że [A] jest mniejszy
    od [B], gdyż ma mniej (lub tyle samo) elementów, tak istnieje surjekcji
    [f : A -> B] oznacza, że [A] jest większy niż [B], gdyż ma więcej (lub
    tyle samo) elementów.

    Jest tak na mocy samej definicji: każdy element przeciwdziedziny jest
    obrazem jakiegoś elementu dziedziny. Nie jest powiedziane, ile jest
    tych elementów, ale wiadomo, że co najmniej jeden.

    Podobnie jak w przypadku injekcji, fakt że złożenie surjekcji jest
    surjekcją możemy traktować jako stwierdzenie, że porządek, jakim jest
    istnienie surjekcji, jest przechodni. (TODO) *)

(** **** Ćwiczenie *)

(** Pokaż, że nie istnieje surjekcja z [unit] w [bool]. Oznacza to, że [unit]
    nie jest większy niż [bool]. *)

Lemma no_sur_unit_bool :
  ~ exists f : unit -> bool, surjective f.
(* begin hide *)
Proof.
  unfold surjective, not; intros.
  destruct H as [f H]. destruct (H true), (H false).
  destruct x, x0. rewrite H0 in H1. inversion H1.
Qed.
(* end hide *)

(** Pokaż, że istnieje surjekcja z każdego typu niepustego w [unit].
    Oznacza to, że każdy typ niepusty ma co najmniej tyle samo elementów,
    co [unit], tzn. każdy typ nie pusty ma co najmniej jeden element. *)

Lemma sur_A_unit :
  forall (A : Type) (nonempty : A), exists f : A -> unit, surjective f.
(* begin hide *)
Proof.
  unfold surjective; intros. exists (fun _ => tt).
  destruct b. exists nonempty. trivial.
Qed.
(* end hide *)

(** * Bijekcje *)

(* begin hide *)
(* TODO: o bijekcjach/injekcjach/surjekcjach z HoTTowej perspektywy. *)
(* end hide *)

Definition bijective {A B : Type} (f : A -> B) : Prop :=
  injective f /\ surjective f.

(** Po łacinie przedrostek "bi-" oznacza "dwa". Bijekcja to funkcja, która
    jest zarówno injekcją, jak i surjekcją. *)

Lemma id_bij : forall A : Type, bijective (@id A).
Proof.
  split; intros.
    apply id_injective.
    apply id_sur.
Qed.

Lemma S_not_bij : ~ bijective S.
Proof.
  unfold bijective; intro. destruct H.
  apply S_not_surjective. assumption.
Qed.

(** Pozostawię przykłady bez komentarza — są one po prostu konsekwencją tego,
    co już wiesz na temat injekcji i surjekcji.

    Ponieważ bijekcja jest surjekcją, to każdy element jej przeciwdziedziny
    jest obrazem jakiegoś elementu jej dziedziny (obraz elementu [x] to po
    prostu [f x]). Ponieważ jest injekcją, to element ten jest unikalny.

    Bijekcja jest więc taką funkcją, że każdy element jej przeciwdziedziny
    jest obrazem dokładnie jednego elementu jej dziedziny. Ten właśnie fakt
    wyraża poniższa definicja alternatywna.

    TODO: [exists!] nie zostało dotychczas opisane, a chyba nie powinno być
    opisane tutaj. *)

Definition bijective' {A B : Type} (f : A -> B) : Prop :=
  forall b : B, exists! a : A, f a = b.

(** **** Ćwiczenie *)

(** Udowodnij, że obie definicje są równoważne. *)

Lemma bijective_bijective' :
  forall (A B : Type) (f : A -> B),
    bijective f <-> bijective' f.
(* begin hide *)
Proof.
  unfold bijective, bijective', injective, surjective; split; intros.
    destruct H as [Hinj Hsur]. destruct (Hsur b) as [a H].
      exists a. red. split; try assumption. intros. apply Hinj.
      rewrite H, H0. reflexivity.
    split; intros.
      destruct (H (f x)) as [a Ha]. destruct Ha as [Ha1 Ha2].
        rewrite <- (Ha2 x).
          apply Ha2. rewrite H0. reflexivity.
          reflexivity.
      destruct (H b) as [a [H1 H2]]. exists a. assumption.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

Require Import D5.

Fixpoint unary (n : nat) : list unit :=
match n with
    | 0 => []
    | S n' => tt :: unary n'
end.

(** Funkcja [unary] reprezentuje liczbę naturalną [n] za pomocą listy
    zawierającej [n] kopii termu [tt]. Udowodnij, że [unary] jest
    bijekcją. *)

Lemma unary_bij : bijective unary.
(* begin hide *)
Proof.
  unfold bijective, injective, surjective. split.
    induction x as [| y]; induction x' as [| y']; cbn in *.
      trivial.
      inversion 1.
      inversion 1.
      inversion 1. f_equal. apply IHy. assumption.
    intro. exists (length b). induction b as [| h t]; cbn.
      trivial.
      destruct h. f_equal. assumption.
Qed.
(* end hide *)

(** Jak już powiedzieliśmy, bijekcje dziedziczą właściwości, które mają
    zarówno injekcje, jak i surjekcje. Wobec tego możemy skonkludować,
    że złożenie bijekcji jest bijekcją. Nie mają one jednak "dziwnej
    własciwości".

    TODO UWAGA: od teraz twierdzenia, które pozostawię bez dowodu, z
    automatu stają się ćwiczeniami. *)

Lemma bij_comp :
  forall (A B C : Type) (f : A -> B) (g : B -> C),
    bijective f -> bijective g -> bijective (f .> g).
(* begin hide *)
Proof.
  unfold bijective, comp; intros. destruct H, H0. split.
    apply inj_comp; assumption.
    apply sur_comp; assumption.
Qed.
(* end hide *)

(** Bijekcje mają też interpretacje w idei rozmiaru oraz ilości elementów.
    Jeżeli istnieje bijekcja [f : A -> B], to znaczy, że typy [A] oraz [B]
    mają dokładnie tyle samo elementów, czyli są "tak samo duże".

    Nie powinno nas zatem dziwić, że relacja istnienia bijekcji jest
    relacją równoważności:
    - każdy typ ma tyle samo elementów, co on sam
    - jeżeli typ [A] ma tyle samo elementów co [B], to [B] ma tyle samo
      elementów, co [A]
    - jeżeli [A] ma tyle samo elementów co [B], a [B] tyle samo elementów
      co [C], to [A] ma tyle samo elementów co [C] *)

(** **** Ćwiczenie *)

(** Jeżeli między [A] i [B] istnieje bijekcja, to mówimy, że [A] i [B] są
    równoliczne (ang. equipotent). Pokaż, że relacja równoliczności jest
    relacją równoważności. TODO: prerekwizyt: relacje równoważności *)

Definition equipotent (A B : Type) : Prop :=
  exists f : A -> B, bijective f.

Notation "A ~~ B" := (equipotent A B) (at level 10).

(** Równoliczność [A] i [B] będziemy oznaczać przez [A ~ B]. Nie należy
    notacji [~] mylić z notacją [~] oznaczającej negację logiczną. Ciężko
    jednak jest je pomylić, gdyż pierwsza zawsze bierze dwa argumenty, a
    druga tylko jeden. *)

Lemma equipotent_refl :
  forall A : Type, A ~~ A.
(* begin hide *)
Proof.
  red. intro. exists id. apply id_bij.
Qed.
(* end hide *)

Lemma equipotent_sym :
  forall A B : Type, A ~~ B -> B ~~ A.
(* begin hide *)
Proof.
  unfold equipotent, bijective; intros. destruct H as [f [Hinj Hsur]].
  red in Hsur. assert (B -> A).
    intro b. Fail destruct (Hsur b) as [a H].
Admitted.
(* end hide *)

Lemma equipotent_trans :
  forall A B C : Type, A ~~ B -> B ~~ C -> A ~~ C.
(* begin hide *)
Proof.
  unfold equipotent; intros. destruct H as [f Hf], H0 as [g Hg].
  exists (f .> g). apply bij_comp; assumption.
Qed.
(* end hide *)

(** * Inwolucje *)

Definition involutive {A : Type} (f : A -> A) : Prop :=
  forall x : A, f (f x) = x.

(** Kolejnym ważnym (choć nie aż tak ważnym) rodzajem funkcji są inwolucje.
    Po łacinie "volvere" znaczy "obracać się". Inwolucja to funkcja, która
    niczym Chuck Norris wykonuje półobrót — w tym sensie, że zaaplikowanie
    jej dwukrotnie daje cały obrót, a więc stan wyjściowy.

    Mówiąc bardziej po ludzku, inwolucja to funkcja, która jest swoją własną
    odwrotnością. Spotkaliśmy się już z przykładami inwolucji: najbardziej
    trywialnym z nich jest funkcja identycznościowa, bardziej oświecającym
    zaś funkcja [rev], która odwraca listę — odwrócenie listy dwukrotnie
    daje wyjściową listę. Inwolucją jest też [negb]. *)

Lemma id_inv :
  forall A : Type, involutive (@id A).
(* begin hide *)
Proof.
  red; intros. trivial.
Qed.
(* end hide *)

Lemma rev_inv :
  forall A : Type, involutive (@rev A).
(* begin hide *)
Proof.
  red; intros. apply rev_inv.
Qed.
(* end hide *)

Lemma negb_inv : involutive negb.
(* begin hide *)
Proof.
  red. destruct x; cbn; trivial.
Qed.
(* end hide *)

(** Żeby nie odgrzewać starych kotletów, przyjrzyjmy się funkcji [weird]. *)

Fixpoint weird {A : Type} (l : list A) : list A :=
match l with
    | [] => []
    | [x] => [x]
    | x :: y :: t => y :: x :: weird t
end.

Lemma weird_inv :
  forall A : Type, involutive (@weird A).
(* begin hide *)
Proof.
  Functional Scheme weird_ind := Induction for weird Sort Prop.
  red; intros. functional induction (weird x); cbn; trivial.
    rewrite IHl. trivial.
Qed.
(* end hide *)

(** Funkcja ta zamienia miejscami bloki elementów listy o długości dwa.
    Nietrudno zauważyć, że dwukrotne takie przestawienie jest identycznością.
    UWAGA TODO: dowód wymaga specjalnej reguły indukcyjnej. *)

Lemma flip_inv :
  forall A : Type, involutive (@flip A A A).
(* begin hide *)
Proof.
  red; intros. unfold flip. extensionality b; extensionality a. trivial.
Qed.
(* end hide *)

(** Inwolucją jest też kombinator [flip], który poznaliśmy na początku
    rozdziału. Przypomnijmy, że zamienia on miejscami argumenty funkcji
    binarnej. Nie dziwota, że dwukrotna taka zamiana daje oryginalną
    funkcję. *)

Goal ~ involutive (@rev nat .> weird).
(* begin hide *)
Proof.
  unfold involutive, not; intro. specialize (H [1; 2; 3]).
  cbn in H. inversion H.
Qed.
(* end hide *)

(** Okazuje się, że złożenie inwolucji wcale nie musi być inwolucją. Wynika
    to z faktu, że funcje [weird] i [rev] są w pewien sposób niekompatybilne
    — pierwsze wywołanie każdej z nich przeszkadza drugiemu wywołaniu drugiej
    z nich odwrócić efekt pierwszego wywołania. *)

Lemma comp_inv :
  forall (A : Type) (f g : A -> A),
    involutive f -> involutive g -> f .> g = g .> f -> involutive (f .> g).
(* begin hide *)
Proof.
  unfold involutive. intros.
  assert (forall x, (f .> g) x = (g .> f) x).
    rewrite H1. trivial.
    unfold comp in *. rewrite <- H2, H, H0. trivial.
Qed.
(* end hide *)

(** Kryterium to jest rozstrzygające — jeżeli inwolucje komutują ze sobą
    (czyli są "kompatybilne", [f .> g = g .> f]), to ich złożenie również
    jest inwolucją. *)

Lemma inv_bij :
  forall (A : Type) (f : A -> A), involutive f -> bijective f.
(* begin hide *)
Proof.
  unfold involutive, bijective; intros. split; red; intros.
    rewrite <- (H x), <- (H x'). rewrite H0. trivial.
    exists (f b). apply H.
Qed.
(* end hide *)

(** Ponieważ każda inwolucja ma odwrotność (którą jest ona sama), każda
    inwolucja jest z automatu bijekcją. *)

(* begin hide *)
Fixpoint count_inv (n : nat) : nat :=
match n with
    | 0 => 1
    | 1 => 1
    | S ((S n'') as n') => count_inv n' + (n - 1) * count_inv n''
end.

Compute count_inv 6.
Compute map count_inv [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11].
(* end hide *)

(** **** Ćwiczenie *)

(** Rozważmy funkcje rzeczywiste f(x) = ax^n, f(x) = ax^(-n), f(x) = sin(x),
    f(x) = cos(x), f(x) = a/x, f(x) = a - x, f(x) = e^x. Które z nich są
    inwolucjami? *)

(** * Uogólnione inwolucje *)

(** Pojęcie inwolucji można nieco uogólnić. Żeby to zrobić, przeformułujmy
    najpierw definicję inwolucji. *)

Definition involutive' {A : Type} (f : A -> A) : Prop :=
  f .> f = id.

(** Nowa definicja głosi, że inwolucja to taka funkcja, że jej złożenie
    ze sobą jest identycznością. Jeżeli funkcje [f .> f] i [id A]
    zaaplikujemy do argumentu [x], otrzymamy oryginalną definicję. Nowa
    definicja jest równoważna starej na mocy aksjomatu ekstensjonalności
    dla funkcji. *)

Lemma involutive_involutive' :
  forall (A : Type) (f : A -> A), involutive f <-> involutive' f.
(* begin hide *)
Proof.
  unfold involutive, involutive'; split; intros.
    unfold comp, id. extensionality x. apply H.
    change x with (id x) at 2. rewrite <- H. reflexivity.
Qed.
(* end hide *)

(** Pójdźmy o krok dalej. Zamiast składania [.>] użyjmy kombinatora [iter 2],
    który ma taki sam efekt. *)

Definition involutive'' {A : Type} (f : A -> A) : Prop :=
  iter f 2 = id.

Lemma involutive'_involutive'' :
  forall (A : Type) (f : A -> A),
    involutive' f <-> involutive'' f.
(* begin hide *)
Proof.
  unfold involutive', involutive''; split; intros.
    unfold iter. rewrite <- H. reflexivity.
    assumption.
Qed.
(* end hide *)

(** Droga do uogólnienia została już prawie przebyta. Nasze dotychczasowe
    inwolucje nazwiemy uogólnionymi inwolucjami rzędu 2. Definicję
    uogólnionej inwolucji otrzymamy, zastępując w definicji 2 przez [n]. *)

Definition gen_involutive
  {A : Type} (n : nat) (f : A -> A) : Prop :=
    iter f n = id.

(** Nie żeby pojęcie to było jakoś szczególnie często spotykane lub nawet
    przydatne — wymyśliłem je na poczekaniu. Spróbujmy znaleźć jakąś
    uogólnioną inwolucję o rzędzie większym niż 2. *)

Fixpoint weirder {A : Type} (l : list A) : list A :=
match l with
    | [] => []
    | [x] => [x]
    | [x; y] => [x; y]
    | x :: y :: z :: t => y :: z :: x :: weirder t
end.

Compute weirder [1; 2; 3; 4; 5].
(* ===> = [2; 3; 1; 4; 5] : list nat *)

Compute iter weirder 3 [1; 2; 3; 4; 5].
(* ===> = [1; 2; 3; 4; 5] : list nat *)

Lemma weirder_inv_3 :
  forall A : Type, gen_involutive 3 (@weirder A).
(* begin hide *)
Proof.
  Functional Scheme weirder_ind := Induction for weirder Sort Prop.
  unfold gen_involutive; intros. extensionality l.
  functional induction (weirder l); cbn; trivial.
  unfold iter in IHl0. rewrite IHl0. reflexivity.
Qed.
(* end hide *)

(** * Idempotencja *)

Definition idempotent {A : Type} (f : A -> A) : Prop :=
  forall x : A, f (f x) = f x.

(** Kolejnym rodzajem funkcji są funkcje idempotente. Po łacinie "idem"
    znaczy "taki sam", zaś "potentia" oznacza "moc". Funkcja idempotentna
    to taka, której wynik jest taki sam niezależnie od tego, ile razy
    zostanie zaaplikowana.

    Przykłady można mnożyć. Idempotentne jest wciśnięcie guzika w windzie
    — jeżeli np. wciśniemy "2", to po wjechaniu na drugi piętro kolejne
    wciśnięcia guzika "2" nie będą miały żadnego efektu.

    Idempotentne jest również sortowanie. Jeżeli posortujemy listę, to jest
    ona posortowana i kolejne sortowania niczego w niej nie zmienią. Problemem
    sortowania zajmiemy się w przyszłych rozdziałach. *)

Lemma id_idem :
  forall A : Type, idempotent (@id A).
(* begin hide *)
Proof.
  unfold idempotent. trivial.
Qed.
(* end hide *)

Lemma const_idem :
  forall (A B : Type) (b : B), idempotent (const b).
(* begin hide *)
Proof.
  unfold idempotent. trivial.
Qed.
(* end hide *)

(* begin hide *)
Require Import X3.
(* end hide *)

Lemma take_idem :
  forall (A : Type) (n : nat), idempotent (@take A n).
(* begin hide *)
Proof.
  unfold idempotent; intros.
  rewrite take_length'.
    reflexivity.
    rewrite length_take. apply Nat.le_min_r.
Qed.
(* end hide *)

(** Identyczność jest idempotentna — niezrobienie niczego dowolną ilość
    razy jest wszakże ciągle niezrobieniem niczego. Podobnież funkcja
    stała jest idempotentna — zwracanie tej samej wartości daje zawsze
    ten sam efekt, niezależnie od ilości powtórzeń.

    Ciekawszym przykładem, który jednak nie powinien cię zaskoczyć, jest
    funkcja [take] dla dowolnego [n : nat]. Wzięcie [n] elementów z listy
    [l] daje nam listę mającą co najwyżej [n] elementów. Próba wzięcia
    [n] elementów z takiej listy niczego nie zmieni, gdyż jej długość jest
    mniejsza lub równa ilości elementów, które chcemy wziąć. *)

Lemma comp_idem :
  forall (A : Type) (f g : A -> A),
    idempotent f -> idempotent g -> f .> g = g .> f ->
      idempotent (f .> g).
(* begin hide *)
Proof.
  unfold idempotent. intros.
  assert (forall x, (f .> g) x = (g .> f) x).
    rewrite H1. trivial.
    unfold comp in *. rewrite <- H2, H, H0. trivial.
Qed.
(* end hide *)

(** Jeżeli chodzi o składanie funkcji idempotentnych, sytuacja jest podobna
    do tej, jaka jest udziałem inwolucji. *)

(* begin hide *)
(** * Uogólniona idempotencja (TODO) *)

(** Podobnie jak w przypadku inwolutywności, pojęcie idempotencji możemy
    uogólnić na pojęcie idempotencji rzędu n — po zaaplikowaniu funkcji
    n razy kolejne aplikacje przestają mieć jakiekolwiek efekty. *)

Definition gen_idempotent
  {A : Type} (n : nat) (f : A -> A) : Prop :=
    forall k : nat, iter f (k + n) = iter f n.

(** Zdaje mi się ono jednak być mocno bezużyteczne.*)

(* TODO: wymyślić jakieś przykłady. *)

(** * Punkty stałe (TODO) *)

(** Kolejnym ważnym pojęciem jest pojęcie punktu stałego (ang. fixed point,
    często skracane do fixpoint). Właśnie od niego bierze się nazwa
    komendy [Fixpoint], służącej do definiowania funkcji rekurencyjnych. *)

Definition fixpoint {A : Type} (f : A -> A) (x : A)
  : Prop := f x = x.

(* end hide *)

(** * Skracalność (TODO) *)

(** Tutaj o lewej i prawej skracalności, czyli mono- i epi- morfizmy. *)