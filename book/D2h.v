(** * D2h: Metoda induktywnej dziedziny *)

Require Import List.
Import ListNotations.

Require Import Arith Lia.

From Typonomikon Require Import D5.
From Typonomikon Require Export D1n.

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

(** * Porządny predykat dziedziny *)

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

(** ** Eliminacja zdań i irrelewancja dowodów *)

(** Cóż, nie da się i nie dziwota - gdyby się dało, to zrobiliśmy tak
    już na samym początku. Powód porażki jest całkiem prozaiczny -
    nie możemy definiować programów przez dopasowanie do wzorca dowodów,
    czyli parafrazując, nie możemy konstruować elementów typów żyjących
    w sortach [Set] ani [Type] przez eliminację dowodów zdań, czyli
    elementów typów żyjących w sorcie [Prop].

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

(** ** Inwersja na predykacie dziedziny *)

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

(** ** Ekstrakcja *)

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

Arguments rot {x} _ _ : rename.

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

(** * Plugin [Equations] *)

(** **** Ćwiczenie *)

(** Zainstaluj plugin
    #<a class='link' href='https://github.com/mattam82/Coq-Equations'>Equations</a>#.
    Przeczytaj
    #<a class='link'
    href='https://raw.githubusercontent.com/mattam82/Coq-Equations/master/doc/equations_intro.v'>
    tutorial</a>#.

    Następnie znajdź jakiś swój dowód przez indukcję, który był skomplikowany
    i napisz prostszy dowód za pomocą komendy [Equations] i taktyki [funelim].
*)

(** * Podsumowanie (TODO) *)