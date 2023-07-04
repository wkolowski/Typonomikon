(** * D2l: Rekursja zagnieżdżona [TODO] *)

Require Import List.
Import ListNotations.

Require Import Arith Lia.

From Typonomikon Require Import D5.
From Typonomikon Require Export D2k.

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