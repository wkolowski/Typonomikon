(** * D2h: Indukcja dobrze ufundowana [TODO] *)

From Typonomikon Require Import D5.

(** * Rekursja dobrze ufundowana *)

(** Typy induktywne są jak domino - każdy term to jedna kostka, indukcja
    i rekursja odpowiadają zaś temu co tygryski lubią najbardziej, czyli
    reakcji łańcuchowej przewracającej wszystkie kostki.

    Typ [unit] to jedna biedna kostka, zaś [bool] to już dwie biedne
    kostki - [true] i [false]. W obu przypadkach nie dzieje się nic
    ciekawego - żeby wszystkie kostki się przewróciły, musimy pchnąć
    palcem każdą z osobna.

    Typ [nat] jest już ciekawszy - są dwa rodzaje kostek, [0] i [S],
    a jeżeli pchniemy kostkę [0] i między kolejnymi kostkami jest
    odpowiedni odstęp, to równy szlaczek kolejnych kostek przewracać
    się będzie do końca świata.

    Podobnie dla typu [list A] mamy dwa rodzaje kostek - [nil] i [cons],
    ale kostki rodzaju [cons] mają różne kolory - są nimi elementy typu
    [A]. Podobnie jak dla [nat], jeżeli pchniemy kostkę [nil] i odstępy
    między kolejnymi kostkami są odpowiednie, to kostki będą przewracać
    się w nieskończoność. Tym razem jednak zamiast jednego szaroburego
    szlaczka będzie multum kolorowych szlaczków o wspólnych początkach
    (no chyba, że [A = unit] - wtedy dostaniemy taki sam bury szlaczek
    jak dla [nat]).

    Powyższe malownicze opisy przewracających się kostek domina bardziej
    przywodzą na myśl indukcję, niż rekursję, chociaż wiemy już, że jest
    to w sumie to samo. Przyjmują one perspektywę "od przodu" - jeżeli
    przewrócimy początkową kostkę i niczego nie spartaczyliśmy, kolejne
    kostki będą przewracać się już same.

    Co to znaczy, że niczego nie spartaczyliśmy, pytasz? Tutaj przydaje
    się spojrzenie na nasze domino "od tyłu". Żeby kostka domina się
    przewróciła, muszą przewrócić się na nią wszystkie bezpośrednio
    poprzedzające ją kostki, a żeby one się przewróciły, to przewrócić
    muszą się wszystkie poprzedzające je kostki i tak dalej. W związku
    z tym możemy powiedzieć, że kostka jest dostępna, jeżeli dostępne
    są wszystkie kostki ją poprzedzające.

    Jeszcze jeden drobny detal: kiedy dostępne są kostki, które nie mają
    żadnych poprzedzających kostek? Odpowiedź: zawsze, a dowodem na to
    jest nasz palec, który je przewraca.

    W ten oto wesoły sposób udało nam się uzyskać definicję elementu
    dostępnego oraz relacji dobrze ufundowanej. *)

Inductive Acc {A : Type} (R : A -> A -> Prop) (x : A) : Prop :=
| Acc_intro : (forall y : A, R y x -> Acc R y) -> Acc R x.

(** Kostki domina reprezentuje typ [A], zaś relacja [R] to sposób ułożenia
    kostek, a [x] to pewna konkretna kostka domina. Konstruktor [Acc_intro]
    mówi, że kostka [x] jest dostępna w układzie domina [R], jezeli każda
    kostka [y], która poprzedza ją w układzie [R], również jest dostępna.

    Mniej poetycko: element [x : A] jest [R]-dostępny, jeżeli każdy
    [R]-mniejszy od niego element [y : A] również jest [R]-dostępny. *)

Definition well_founded {A : Type} (R : A -> A -> Prop) : Prop :=
  forall x : A, Acc R x.

(** Układ kostek reprezentowany przez [R] jest niespartaczony, jeżeli każda
    kostka domina jest dostępna.

    Mniej poetycko: relacja [R] jest dobrze ufundowana, jeżeli każde [x : A]
    jest [R]-dostępne.

    Uwaga: typem naszego układu kostek nie jest [A -> A -> Prop], lecz
    [A -> A -> Type], a zatem [R] jest tak naprawdę indeksowaną rodziną
    typów, a nie relacją. Różnica między relacją i rodziną typów jest
    taka, że relacja, gdy dostanie argumenty, zwraca zdanie, czyli coś
    typu [Prop], a rodzina typów, gdy dostanie argumenty, zwraca typ,
    czyli coś typu [Type]. Tak więc pojęcie rodziny typów jest ogólniejsze
    niż pojęcie relacji. Ta ogólność przyda się nam za kilka chwil aby nie
    musieć pisać wszystkiego dwa razy. *)

(** **** Ćwiczenie *)

(** Sprawdź, czy relacje [<=], [<] są dobrze ufundowane. *)

(* begin hide *)
Lemma le_not_Acc :
  forall n : nat, Acc le n -> False.
Proof.
  induction 1. apply (H0 x). reflexivity.
Qed.

Lemma le_not_wf : ~ well_founded le.
Proof.
  unfold well_founded. intro.
  apply le_not_Acc with 0. apply H.
Qed.

Lemma wf_lt : well_founded lt.
Proof.
  unfold well_founded.
  induction x as [| n'].
    constructor. inversion 1.
    constructor. intros a Ha. constructor. intros b Hb.
      apply IHn'. apply Nat.lt_le_trans with a.
        assumption.
        apply le_S_n. assumption.
Defined.

(* end hide *)

(** **** Ćwiczenie *)

(** Pokaż, że relacja dobrze ufundowana jest antyzwrotna oraz zinterpretuj
    ten fakt (tzn. powiedz, o co tak naprawdę chodzi w tym stwierdzeniu). *)

(* begin hide *)
Lemma Acc_antirefl :
  forall (A : Type) (R : A -> A -> Prop) (x : A),
    Acc R x -> ~ R x x.
Proof.
  induction 1. intro. apply (H0 x); assumption.
Qed.
(* end hide *)

Lemma wf_antirefl :
  forall (A : Type) (R : A -> A -> Prop),
    well_founded R -> forall x : A, ~ R x x.
(* begin hide *)
Proof.
  unfold well_founded. intros.
  apply Acc_antirefl. apply H.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Sprawdź, czy dobrze ufundowana jest następująca relacja porządku:
    wszystkie liczby parzyste są mniejsze niż wszystkie liczby nieparzyste,
    zaś dwie liczby o tej samej parzystości porównujemy według zwykłego
    porządku [<]. *)

(* begin hide *)
(** TODO *)
(* end hide *)

(** **** Ćwiczenie *)

(** Sprawdź, czy dobrze ufundowana jest następująca relacja porządku
    (mam nadzieję, że obrazek jest zrozumiały):
    0 < 1 < ... < ω < ω + 1 < ... < 2 * ω

     Oczywiście najpierw musisz wymyślić, w jaki sposób zdefiniować taką
     relację. Uwaga: istnieje bardzo sprytne rozwiązanie. *)

(* begin hide *)
Require Import Lia.

Module Ex.

Inductive T : Type :=
| from0 : nat -> T
| fromω : nat -> T
| ωω : T.

Definition R (x y : T) : Prop :=
match x, y with
| from0 n, from0 m => n < m
| from0 _, _ => True
| fromω _, from0 _ => False
| fromω n, fromω m => n < m
| fromω _, _ => True
| ωω, _ => False
end.

Lemma R_trans :
  forall a b c : T, R a b -> R b c -> R a c.
Proof.
  induction a as [n | n |];
  destruct b as [m | m |],
           c as [k | k |];
  cbn; lia.
Qed.

Lemma Acc_from0 :
  forall n : nat, Acc R (from0 n).
Proof.
  induction n as [| n']; cbn.
    constructor. destruct y; inversion 1.
    constructor. destruct y; inversion 1; subst.
      assumption.
      inversion IHn'. constructor. intros. apply H0.
        eapply R_trans; eauto.
Qed.

Lemma Acc_fromω :
  forall n : nat, Acc R (fromω n).
Proof.
  induction n as [| n']; cbn.
    constructor. destruct y; inversion 1. apply Acc_from0.
    constructor. destruct y; inversion 1; subst.
      apply Acc_from0.
      assumption.
      inversion IHn'. constructor. intros. apply H0.
        eapply R_trans; eauto.
Qed.

Lemma wf_R : well_founded R.
Proof.
  unfold well_founded.
  destruct x as [m | m |].
    apply Acc_from0.
    apply Acc_fromω.
    constructor. destruct y; inversion 1.
      apply Acc_from0.
      apply Acc_fromω.
Qed.

End Ex.
(* end hide *)

(** Nasza bajka powoli zbliża się do końca. Czas udowodnić ostateczne
    twierdzenie, do którego dążyliśmy: jeżeli układ kostek [R] jest
    niespartaczony (czyli gdy każda kostka jest dostępna), to każda
    kostka się przewraca. *)

Lemma well_founded_rect :
  forall
    (A : Type) (R : A -> A -> Prop)
    (wf : well_founded R) (P : A -> Type),
      (forall x : A, (forall y : A, R y x -> P y) -> P x) ->
        forall x : A, P x.
Proof.
  intros A R wf P H x.
  unfold well_founded in wf. specialize (wf x).
  induction wf as [x _ IH].
  apply H. exact IH.
Defined.

(** Podobnie jak poprzednio, [A] to typ kostek domina, [R] to układ kostek,
    zaś [wf : well_founded R] to dowód na to, że układ jest niespartaczony.
    [P : A -> Type] to dowolna rodzina typów indeksowana przez [A], ale
    możemy myśleć, że [P x] znaczy "kostka x się przewraca". Mamy jeszcze
    hipotezę, która głosi, że kostka [x] przewraca się, gdy przewraca się
    każda kostka, która poprzedza ją w układzie [R].

    Dowód jest banalny. Zaczynamy od wprowadzenia zmiennych i hipotez do
    kontekstu. Następnie odwijamy definicję [well_founded]. Teraz hipoteza
    [wf] głosi, że każde [x : A] jest dostępne. Skoro tak, to specjalizujemy
    ją dla naszego konkretnego [x], które mamy w kontekście.

    Wiemy już zatem, że [x] jest dostępne. Jest to kluczowy fakt, gdyż
    oznacza to, że wszystkie kostki domina poprzedzające [x] również są
    dostępne. Co więcej, [Acc] jest zdefiniowane induktywnie, więc możemy
    pokazać, że [x] się przewraca, właśnie przez indukcję po dowodzie
    dostępności [x].

    Przypadek jest jeden (co nie znaczy, że nie ma przypadków bazowych -
    są nimi kostki domina, których nic nie poprzedza): musimy pokazać, że
    [x] się przewraca przy założeniu, że wszystkie poprzedzające je kostki
    również się przewracają. To, że [x] się przewraca, wynika z hipotezy
    [H]. Pozostaje nam jedynie pokazać, że przewraca się wszystko, co jest
    przed nim, ale to jest faktem na mocy hipotezy indukcyjnej [IH]. *)

Lemma well_founded_ind :
  forall
    (A : Type) (R : A -> A -> Prop)
    (wf : well_founded R) (P : A -> Type),
      (forall x : A, (forall y : A, R y x -> P y) -> P x) ->
        forall x : A, P x.
Proof.
  intros A R wf P H x.
  apply (well_founded_rect _ _ wf _ H).
Qed.

(** Poprzednie twierdzenie, czyli [well_founded_rect], to twierdzenie o
    rekursji dobrze ufundowanej. Powyższe, czyli [well_founded_ind],
    które jest jego specjalizacją dla relacji binarnych (czyli bytów o
    typie [A -> A -> Prop]), możemy nazwać twierdzeniem o indukcji dobrze
    ufundowanej.

    Upewnij się, że dobrze rozumiesz oba twierdzenia, a także pojęcia
    dostępności i dobrego ufundowania, gdyż są one bardzo ważne przy
    rozwiązywaniu poważniejszych problemów.

    Co to są "poważniejsze problemy"? Mam oczywiście na myśli dowodzenie
    twierdzeń i definiowanie funkcji, którego nie da się zrobić za pomocą
    prostej indukcji albo banalnego dopasowania do wzorca. W tego typu
    sytuacjach nieodzowne będzie skorzystanie z indukcji i rekursji
    dobrze ufundowanej, o czym przekonamy się już natychmiast zaraz. *)

Definition div : nat -> nat -> nat.
Proof.
  apply (@well_founded_rect nat lt wf_lt (fun _ => nat -> nat)).
  intros n IH m.
  destruct (le_lt_dec (S m) n).
    2: exact 0.
    refine (1 + IH (n - S m) _ m). abstract lia.
Defined.

(* begin hide *)

(** TODO: wprowadzić kombinator [abstract] za pierwszym razem, gdy użyta
    zostanie taktyka [lia]. *)

(* end hide *)

(** Poważniejszym problemem jest bowiem definicja dzielenia, z którą borykamy
    się od samiuśkiego początku niniejszego rozdziału. Powyższy kawałek kodu
    jest (nieudaną, jak się okaże) próbą uporania się z tym problemem.

    Definiować będziemy w trybie dowodzenia, gdyż przy posługiwaniu się
    rekursją dobrze ufundowaną zazwyczaj tak jest dużo łatwiej. Zaczynamy
    od zaaplikowania reguły rekursji dobrze ufundowanej dla typu [nat] i
    porządku [<] (no i rzecz jasna [wf_lt], czyli dowodu na to, że [lt]
    jest dobrze ufundowany - bez tego ani rusz). Po typach widać, że
    rekursja będzie się odbywać po pierwszym argumencie. Wprowadzamy też
    zmienne do kontekstu. *)

Check le_lt_dec.
(* ===> le_lt_dec : forall n m : nat, {n <= m} + {m < n} *)

(** Następnie musimy sprawdzić, czy dzielna (czyli [n]) jest mniejsza od
    dzielnika (czyli [S m] - zauważ, że definiujemy tutaj "sprytną" wersję
    dzielenia, tzn. [div n m] = [n/(m + 1)], żeby uniknąć problemów z
    dzieleniem przez [0]). Jeżeli tak, wynikiem jest [0]. Jeżeli nie,
    wynikiem jest wynik wywołania rekurencyjnego na argumencie [n - S m]
    powiększony o [1].

    Na koniec musimy jeszcze tylko pokazać, że argument wywołania
    rekurencyjnego, czyli [n - S m], jest mniejszy od argumentu
    obecnego wywołania, czyli [n]. Żeby za bardzo nie pobrudzić
    sobie rąk arytmetyką, zostawiamy ten cel taktyce [lia], ale
    zawijamy jej użycie w kombinator [abstract], który zapobiega
    "wylaniu się" rozumowania taktyki [lia] do definicji. *)

Print div.
(* ===>
  div =
  well_founded_rect nat lt wf_lt (fun _ : nat => nat -> nat)
    (fun (n : nat)
         (IH : forall y : nat, y < n -> nat -> nat)
         (m : nat) =>
    let s := le_lt_dec (S m) n in
      match s with
      | left l => 1 + IH (n - S m) (div_subproof n m l) m
      | right _ => 0
      end)
    : nat -> nat -> nat *)

Check div_subproof.
(* ===> div_subproof
          : forall n m : nat, S m <= n -> n - S m < n *)

Print div_subproof.
(* ===> dużo różnych głupot, szkoda pisać *)

(** Mówiąc wprost, taktyka [abstract lia] zamiast wstawiać do definicji
    całe rozumowanie, tak jak zrobiłaby to taktyka [lia], dowodzi sobie
    na boku odpowiedni lemat arytmetyczny, nazywa go [div_subproof] i
    dowodzi celu za jego pomocą. *)

Compute div 5 2.
(* ===> = 1 : nat *)

(** Jak widać, definicja przechodzi bez problemu, a nasza funkcja elegancko
    się oblicza (pamiętaj, że [div 5 2] to tak naprawdę [5/3], więc wynikiem
    faktycznie powinno być [1]).

    Jednak nie samymi definicjami żyje człowiek - czas trochę podowodzić.
    Spodziewamy się wszakże, że nasze dzielenie spełnia wszystkie
    właściwości, których się po nim spodziewamy, prawda? *)

Lemma div_0_r :
  forall n : nat, div n 0 = n.
Proof.
  apply (well_founded_ind _ _ wf_lt).
  intros. unfold div. cbn. (* O Jezu, a cóż to za wojacy? *)
Abort.

(** Niestety jednak, jak to w życiu, nie ma kolorowo.

    Powyższy lemat głosi, że [n/1 = n]. Ponieważ [div] jest zdefiniowane
    za pomocą rekursji dobrze ufundowanej, to dowodzić będziemy oczywiście
    za pomocą indukcji dobrze ufundowanej. Tak, będziemy dowodzić, hmmm...
    cóż... tylko jak?

    Sytuacja wygląda beznadziejnie. Nie żeby lemat był nieprawdziwy - co to,
    to nie. Po prostu próba odwinięcia definicji i policzenia czegokolwiek
    daje inny wynik, niż byśmy chcieli - część definicji ukryta dotychczas
    w [div_subproof] wylewa się i zaśmieca nam ekran.

    Problem nie pochodzi jednak od taktyki [lia] (ani od [abstract lia]).
    Jest on dużo ogólniejszy i polega na tym, że wewnątrz definicji funkcji
    pojawiają się dowody, które są wymagane przez [well_founded_rect], ale
    które zaorywują jej obliczeniową harmonię.

    Nie jesteśmy jednak (jeszcze) skazani na porażkę. Spróbujemy uporać się
    z tą przeszkodą dzięki _równaniu rekurencyjnemu_. Równanie rekurencyjne
    to lemat, którego treść wygląda dokładnie tak, jak pożądana przez nas
    definicja funkcji, ale która nie może służyć jako definicja z różnych
    powodów, np. dlatego że nie jest strukturalnie rekurencyjna. Dzięki
    równaniu rekurencyjnemu możemy użyć taktyki [rewrite] do przepisania
    wystąpień funkcji [div] do pożądanej postaci zamiast rozwijać je za
    pomocą taktyki [unfold] lub obliczać za pomocą [cbn]. *)

Lemma div_eq :
  forall n m : nat,
    div n m = if n <? S m then 0 else S (div (n - S m) m).
Proof.
  apply (well_founded_ind _ _ wf_lt (fun _ => forall m : nat, _)).
  intros. unfold div. cbn. (* O Jezu, a cóż to za hołota? *)
Admitted.

(** Powyższe równanie dokładnie opisuje, jak powinna zachowywać się funkcja
    [div], ale za definicję służyć nie może, gdyż Coq nie byłby w stanie
    rozpoznać, że [n - S m] jest podtermem [n]. Zauważ, że używamy tu [<?]
    (czyli [ltb]) zamiast [le_lt_dec]. Możemy sobie na to pozwolić, gdyż
    użycie [le_lt_dec] w faktycznej definicji wynikało jedynie z tego, że
    potrzebowaliśmy dowodu odpowiedniego faktu arytmetycznego, żeby użyć
    go jako argumentu wywołania rekurencyjnego.

    Niestety próba udowodnienia tego równania rekurencyjnego musi skończyć
    się taką samą porażką, jak próba udowodnienia [div_0_r]. Przyczyna jest
    taka sama jak ostatnio. Zresztą, naiwnym byłoby spodziewać się, że nam
    się uda - zarówno [div_0_r], jak i [div_eq] to nietrywialne właściwości
    funkcji [div], więc gdybyśmy potrafili udowodnić równanie rekurencyjne,
    to z dowodem [div_0_r] również poradzilibyśmy sobie bez problemu.

    Żeby jednak przekonać się o użyteczności równania rekurencyjnego, jego
    "dowód" kończymy za pomocą komendy [Admitted], która przerywa dowód i
    zamienia twierdzenie w aksjomat. Dzięki temu za chwilę zobaczymy, ile
    moglibyśmy zdziałać, mając równanie rekurencyjne. *)

Lemma div_0_r :
  forall n : nat, div n 0 = n.
Proof.
  apply (well_founded_ind _ _ wf_lt).
  intros n IH. rewrite div_eq.
  destruct (Nat.ltb_spec n 1).
    lia.
    rewrite IH; lia.
Qed.

(** Jak widać, dzięki równaniu rekurencyjnemu dowody przebiegają dość gładko.
    W powyższym zaczynamy od indukcji dobrze ufundowanej po [n] (przy użyciu
    relacji [<] i dowodu [wf_lt]), wprowadzamy zmienne do kontekstu, po czym
    przepisujemy równanie rekurencyjne. Po przeprowadzeniu analizy przypadków
    kończymy za pomocą rozumowań arytmetycznych, używając być może hipotezy
    indukcyjnej. *)

(** **** Ćwiczenie *)

(** Zgadnij, jakie jest polecenie tego ćwiczenia, a następnie wykonaj je. *)

Lemma div_n_n :
  forall n : nat, div (S n) n = 1.
(* begin hide *)
Proof.
  intros n.
  rewrite div_eq, Nat.ltb_irrefl, Nat.sub_diag.
  cbn. reflexivity.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Sprawdź, czy dobrze ufundowane są relacje [le'] i [lt']. Uwaga:
    pierwsze zadanie jest bardzo łatwe, drugie jest piekielnie trudne.
    Jeżeli nie potrafisz rozwiązać go formalnie w Coqu, zrób to na
    kartce nieformalnie - będzie dużo łatwiej.*)

Definition le' (f g : nat -> nat) : Prop :=
  forall n : nat, f n <= g n.

Definition lt' (f g : nat -> nat) : Prop :=
  forall n : nat, f n < g n.

(* begin hide *)
Lemma not_wf_le' : ~ well_founded le'.
Proof.
  intro. apply (wf_antirefl _ _ H id).
  unfold le', id. intro. constructor.
Qed.

Lemma wf_lt' :
  well_founded lt'.
Proof.
  unfold well_founded.
  intro f.
  pose (n := f 0); assert (n = f 0) by reflexivity; clearbody n.
  revert n f H.
  apply (@well_founded_ind _ _ wf_lt
        (fun n => forall f, n = f 0 -> Acc lt' f)).
  intros n IH f Heq. constructor. intros g Hlt.
  unfold lt' in Hlt.
  apply IH with (g 0).
    specialize (Hlt 0). subst. assumption.
    reflexivity.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Niech [B : Type] i niech [R : B -> B -> Prop] będzie relacją dobrze
    ufundowaną. Zdefiniuj po współrzędnych relację porządku na funkcjach
    o typie [A -> B] i rozstrzygnij, czy relacja ta jest dobrze ufundowana.

    Uwaga: w zależności od okoliczności to zadanie może być trudne lub
    łatwe. *)

(* begin hide *)
Module Ex'.

Definition funord
  (A : Type) {B : Type} (R : B -> B -> Prop) (f g : A -> B) : Prop :=
    forall x : A, R (f x) (g x).

Lemma Acc_antirefl :
  forall (A : Type) (R : A -> A -> Prop) (x : A),
    Acc R x -> ~ R x x.
Proof.
  induction 1. intro. apply (H0 x); assumption.
Qed.

Lemma wf_funord_empty :
  forall (A B : Type) (R : B -> B -> Prop),
    (A -> False) -> ~ well_founded (funord A R).
Proof.
  unfold well_founded.
  intros A B R Hempty H.
  pose (f := fun a : A => match Hempty a with end : B); clearbody f.
  apply (Acc_antirefl _ (funord A R) f).
    apply H.
    unfold funord. intro. contradiction.
Qed.

Lemma wf_funord_nonempty :
  forall (A B : Type) (R : B -> B -> Prop) (a : A),
    well_founded R -> well_founded (funord A R).
Proof.
  unfold well_founded.
  intros A B R a Hwf f.
  pose (b := f a).
  assert (b = f a) by reflexivity; clearbody b.
  revert b f H.
  apply (@well_founded_ind B R Hwf
    (fun b => forall f, b = f a -> Acc (funord A R) f)).
  intros b IH f Heq. constructor. intros g Hord.
  apply IH with (g a).
    unfold funord in Hord. specialize (Hord a). subst. apply Hord.
    reflexivity.
Qed.

End Ex'.
(* end hide *)

(** **** Ćwiczenie *)

(** Pokaż, że jeżeli kodziedzina funkcji [f : A -> B] jest dobrze ufundowana
    za pomocą relacji [R : B -> B -> Prop], to jej dziedzina również jest
    dobrze ufundowana. *)

Lemma wf_inverse_image :
  forall (A B : Type) (f : A -> B) (R : B -> B -> Prop),
    well_founded R -> well_founded (fun x y : A => R (f x) (f y)).
(* begin hide *)
Proof.
  unfold well_founded.
  intros A B f R H x.
  pose (b := f x). assert (b = f x) by reflexivity. clearbody b.
  specialize (H b). revert x H0. induction H. rename x into b.
  intros x Heq. constructor. intros.
  eapply H0. rewrite Heq.
    eauto.
    reflexivity.
Defined.
(* end hide *)

(** * Domknięcie przechodnie (TODO) *)

From stdpp Require Import prelude well_founded.

Lemma wf_tc :
  forall {A : Type} (R : A -> A -> Prop),
    wf R -> wf (tc R).
Proof.
  unfold wf.
  intros A R Hwf a.
  specialize (Hwf a).
  induction Hwf as [a H IH].
  constructor.
  intros y Hy.
  induction Hy.
  - by apply IH.
  - by apply IHHy; [| | constructor].
Qed.

Module Fail.

Require Import Equality.

Inductive step : nat -> nat -> Prop :=
| step' : forall n : nat, step n (S n).

Lemma wf_step :
  wf step.
Proof.
  intro n.
  induction n as [| n' IH].
  - constructor. inversion 1.
  - constructor. inversion 1; subst. apply IH.
Defined.

Lemma wf_tc_step :
  wf (tc step).
Proof.
  apply wf_tc, wf_step.
Defined.

End Fail.

(** * Podtermy (TODO) *)

Require Import Relations Equality.
Require Import Relations.Relation_Operators.

Inductive ITree (A : Type) : Type :=
| ILeaf | INode (a : A) (f : nat -> ITree A).

Arguments ILeaf {A}.
Arguments INode {A} _ _.

Inductive itree_child A : ITree A -> ITree A -> Prop :=
| ichild_at n a f : itree_child A (f n) (INode a f).

Lemma tree_child_wf A : well_founded (itree_child A).
Proof.
  intros t; induction t; constructor;
    inversion 1; subst; auto.
Qed.

Definition Subterm {A : Type} : ITree A -> ITree A -> Prop :=
  clos_trans_n1 _ (@itree_child A).

Lemma wf_Subterm_aux :
  forall {A : Type} (t1 t2 : ITree A),
    Subterm t1 t2 -> Acc Subterm t2 -> Acc Subterm t1.
Proof.
  inversion 2.
  apply H1.
  assumption.
Defined.

Lemma wf_Subterm :
  forall A : Type,
    well_founded (@Subterm A).
Proof.
  intros A t.
  induction t as [| a f IH].
  - constructor.
    intros y H.
    dependent induction H; inversion H.
  - constructor.
    intros y H.
    inversion H; subst; clear H.
    + inversion H0; subst.
      apply IH.
    + inversion H0; subst.
      eapply wf_Subterm_aux.
      * apply H1.
      * apply IH.
Defined.

(** * Translacja dobrze ufundowana (TODO) *)

Require Import List.
Import ListNotations.

Require Import Relations Equality.
Require Import Relations.Relation_Operators.

Class WfTranslation (A : Type) : Type :=
{
  smaller : A -> A -> Prop;
  well_founded_smaller : well_founded smaller;
}.

Arguments smaller {A _} _ _.
Arguments well_founded_smaller {A _}.

#[export, refine] Instance WfTranslation_False : WfTranslation False :=
{
  smaller := fun _ _ => False;
}.
Proof.
  now intros [].
Defined.

#[export, refine] Instance WfTranslation_unit : WfTranslation unit :=
{
  smaller := fun _ _ => False;
}.
Proof.
  constructor.
  now intros _ [].
Defined.

Inductive smaller_bool : bool -> bool -> Prop :=
| smaller_false_true : smaller_bool false true.

#[export, refine] Instance WfTranslation_bool : WfTranslation bool :=
{
  smaller := smaller_bool;
}.
Proof.
  constructor.
  intros ? [].
  constructor.
  now inversion 1.
Defined.

Inductive smaller_sum
  {A B : Type} (RA : A -> A -> Prop) (RB : B -> B -> Prop) : A + B -> A + B -> Prop :=
| smaller_sum_l :
    forall (a1 a2 : A), RA a1 a2 -> smaller_sum RA RB (inl a1) (inl a2)
| smaller_sum_r :
    forall (b1 b2 : B), RB b1 b2 -> smaller_sum RA RB (inr b1) (inr b2).

#[export, refine] Instance WfTranslation_sum
  {A B : Type} {WA : WfTranslation A} {WB : WfTranslation B} : WfTranslation (A + B) :=
{
  smaller := smaller_sum smaller smaller;
}.
Proof.
  intros [a | b].
  - pose proof (Acc_a := well_founded_smaller a).
    induction Acc_a as [a H IH].
    constructor.
    inversion 1; subst.
    now apply IH.
  - pose proof (Acc_b := well_founded_smaller b).
    induction Acc_b as [b H IH].
    constructor.
    inversion 1; subst.
    now apply IH.
Defined.

(** Tym razem lewy sumand mniejszy od prawego. *)
Inductive smaller_sum'
  {A B : Type} (RA : A -> A -> Prop) (RB : B -> B -> Prop) : A + B -> A + B -> Prop :=
| smaller_sum'_l :
    forall (a1 a2 : A), RA a1 a2 -> smaller_sum' RA RB (inl a1) (inl a2)
| smaller_sum'_r :
    forall (b1 b2 : B), RB b1 b2 -> smaller_sum' RA RB (inr b1) (inr b2)
| smaller_sum'_l_r :
    forall (a : A) (b : B), smaller_sum' RA RB (inl a) (inr b).

#[export, refine] Instance WfTranslation_sum'
  {A B : Type} {WA : WfTranslation A} {WB : WfTranslation B} : WfTranslation (A + B) :=
{
  smaller := smaller_sum' smaller smaller;
}.
Proof.
  assert (Acc_A : forall a : A, Acc (smaller_sum' smaller smaller) (inl a)).
  {
    intros a.
    pose proof (Acc_a := well_founded_smaller a).
    induction Acc_a as [a H IH].
    constructor.
    inversion 1; subst.
    now apply IH.
  }
  intros [a | b]; [now apply Acc_A |].
  pose proof (Acc_b := well_founded_smaller b).
  induction Acc_b as [b H IH].
  constructor.
  inversion 1; subst.
  - now apply IH.
  - now apply Acc_A.
Defined.

Inductive smaller_prod
  {A B : Type} (RA : A -> A -> Prop) (RB : B -> B -> Prop) : A * B -> A * B -> Prop :=
| smaller_prod_l :
    forall (a1 a2 : A) (b : B), RA a1 a2 -> smaller_prod RA RB (a1, b) (a2, b)
| smaller_prod_r :
    forall (a : A) (b1 b2 : B), RB b1 b2 -> smaller_prod RA RB (a, b1) (a, b2).

#[export, refine] Instance WfTranslation_prod
  {A B : Type} {WA : WfTranslation A} {WB : WfTranslation B} : WfTranslation (A * B) :=
{
  smaller := smaller_prod smaller smaller;
}.
Proof.
  intros [a b].
  pose proof (Acc_a := well_founded_smaller a).
  revert b.
  induction Acc_a as [a Ha IHa].
  intros b.
  constructor.
  intros [a' b']; inversion 1; subst.
  - now apply IHa.
  - clear Ha H H1.
    pose proof (Acc_b := well_founded_smaller b').
    revert a IHa; induction Acc_b as [b' Hb IHb].
    constructor.
    intros [a'' b'']; inversion 1; subst.
    + now apply IHa.
    + now apply IHb.
Defined.

(* TODO: inna translacja dobrze ufundowana dla produktu
Inductive smaller_prod'
  {A B : Type} (RA : A -> A -> Prop) (RB : B -> B -> Prop) : A * B -> A * B -> Prop :=
| smaller_prod'_l :
    forall (a1 a2 a3 : A) (b1 b3 : B),
      RA a1 a2 -> smaller_prod' RA RB (a2, b1) (a3, b3) ->
        smaller_prod' RA RB (a1, b1) (a3, b3)
| smaller_prod'_r :
    forall (a1 a3 : A) (b1 b2 b3 : B),
      RB b1 b2 -> smaller_prod' RA RB (a1, b2) (a3, b3) ->
        smaller_prod' RA RB (a1, b1) (a3, b3).

#[export, refine] Instance WfTranslation_prod'
  {A B : Type} {WA : WfTranslation A} {WB : WfTranslation B} : WfTranslation (A * B) :=
{
  smaller := smaller_prod' smaller smaller;
}.
Proof.
  intros [a b].
  pose proof (Acc_a := well_founded_smaller a).
  revert b.
  induction Acc_a as [a Ha IHa].
  intros b.
  constructor.
  intros [a' b']; inversion 1; subst.
  - now apply IHa.
  - clear Ha H H1.
    pose proof (Acc_b := well_founded_smaller b').
    revert a IHa; induction Acc_b as [b' Hb IHb].
    constructor.
    intros [a'' b'']; inversion 1; subst.
    + now apply IHa.
    + now apply IHb.
Defined.
*)

Inductive smaller_sigT
  {A : Type} {B : A -> Type}
  (RA : A -> A -> Prop) (RB : forall {a : A}, B a -> B a -> Prop)
  : sigT B -> sigT B -> Prop :=
| smaller_sigT_l :
    forall (a1 a2 : A) (b1 : B a1) (b2 : B a2),
      RA a1 a2 -> smaller_sigT RA (@RB) (existT a1 b1) (existT a2 b2)
| smaller_sigT_r :
    forall (a : A) (b1 b2 : B a),
      RB b1 b2 -> smaller_sigT RA (@RB) (existT a b1) (existT a b2).

#[export, refine] Instance WfTranslation_sigT
  {A : Type} {B : A -> Type}
  {WA : WfTranslation A} {WB : forall a : A, WfTranslation (B a)}
  : WfTranslation (sigT B) :=
{
  smaller := smaller_sigT smaller (fun a => @smaller _ (WB a));
}.
Proof.
  intros [a b].
  pose proof (Acc_a := well_founded_smaller a).
  revert b; induction Acc_a as [a Ha IHa]; intros b.
  constructor.
  intros [a' b']; inversion 1; subst.
  - now apply IHa.
  - clear Ha H H1.
    pose proof (Acc_b := well_founded_smaller b').
    revert IHa; induction Acc_b as [b' Hb IHb].
    constructor.
    intros [a'' b'']; inversion 1; subst.
    + now apply IHa.
    + apply IHb; only 3: easy.
Abort.


Module List.

Inductive DirectSubterm {A : Type} : list A -> list A -> Prop :=
| DS_tail : forall (h : A) (t : list A), DirectSubterm t (h :: t).

(** Domknięcie przechodnie relacji [DirectSubterm]. *)
Inductive Subterm {A : Type} : list A -> list A -> Prop :=
| S_step  : forall {l1 l2 : list A}, DirectSubterm l1 l2 -> Subterm l1 l2
| S_trans : forall {l1 l2 l3 : list A}, DirectSubterm l1 l2 -> Subterm l2 l3 -> Subterm l1 l3.

Lemma wf_DirectSubterm :
  forall {A : Type},
    well_founded (@DirectSubterm A).
Proof.
  unfold well_founded.
  now induction x; constructor; inversion 1.
Qed.

Inductive DeepDirectSubterm {A : Type} (R : A -> A -> Prop) : list A -> list A -> Prop :=
| DDS_head : forall (h1 h2 : A) (t : list A), R h1 h2 -> DeepDirectSubterm R (h1 :: t) (h2 :: t)
| DDS_tail : forall (h : A) (t : list A), DeepDirectSubterm R t (h :: t).

Inductive DeepSubterm {A : Type} (R : A -> A -> Prop) : list A -> list A -> Prop :=
| DS_step  :
    forall {l1 l2 : list A},
      DeepDirectSubterm R l1 l2 -> DeepSubterm R l1 l2
| DS_trans :
    forall {l1 l2 l3 : list A},
      DeepDirectSubterm R l1 l2 -> DeepSubterm R l2 l3 -> DeepSubterm R l1 l3.

Lemma wf_DeepDirectSubterm :
  forall {A : Type} {R : A -> A -> Prop},
    well_founded R -> well_founded (DeepDirectSubterm R).
Proof.
  unfold well_founded.
  intros A R wf.
  induction x as [| h t]; constructor; [now inversion 1 |].
  intros t' HDS; inversion HDS; subst; clear HDS; [| easy].
  specialize (wf h1).
  clear H1.
  induction wf.
  constructor.
  intros t'' HDS; inversion HDS; subst; clear HDS; [| easy].
  now apply H0.
Qed.

Lemma DS_DDS :
  forall {A : Type} (l1 l2 : list A),
    DirectSubterm l1 l2 <-> DeepDirectSubterm (fun _ _ => False) l1 l2.
Proof.
  split.
  - now intros []; constructor.
  - now intros []; [| constructor].
Qed.

Lemma DDS_DS :
  forall {A : Type} (R : A -> A -> Prop) (l1 l2 : list A),
    DeepDirectSubterm R l1 l2
      <->
    DirectSubterm l1 l2
      \/
    exists (h1 h2 : A) (t : list A),
      (l1 = h1 :: t)%list /\
      (l2 = h2 :: t)%list /\
      R h1 h2.
Proof.
  split.
  - intros [].
    + now right; eauto 7.
    + now left.
  - intros [| (h1 & h2 & t & -> & -> & r)].
    + now inversion H; right.
    + now left.
Qed.

Inductive VeryDeepDirectSubterm {A : Type} (R : A -> A -> Prop) : list A -> list A -> Prop :=
| VDDS_head :
    forall {h1 h2 : A} (t : list A),
      R h1 h2 -> VeryDeepDirectSubterm R (h1 :: t) (h2 :: t)
| VDDS_tail :
    forall (h : A) {t1 t2 : list A},
      VeryDeepDirectSubterm R t1 t2 -> VeryDeepDirectSubterm R (h :: t1) (h :: t2).

Lemma wf_VeryDeepDirectSubterm :
  forall {A : Type} {R : A -> A -> Prop},
    well_founded R -> well_founded (VeryDeepDirectSubterm R).
Proof.
  unfold well_founded.
  intros A R wf.
  induction x as [| h t]; constructor; [now inversion 1 |].
  intros t' VDDS.
  remember (h :: t) as l.
  revert h t Heql IHt.
  induction VDDS as [h1 h2 t'' r | h' t1 t2 VDDS].
  - intros h t [= -> ->] HAcc.
    clear h r.
    specialize (wf h1).
    revert t HAcc; induction wf as [h1 H IH]; intros t HAcc.
    constructor.
    inversion 1; subst.
    + now apply IH.
    + clear IH. constructor. admit. 
  - intros h t [= -> ->] HAcc.
Restart.
  unfold well_founded.
  intros A R wf [| h t]; constructor; [now inversion 1 |].
  intros t' VDDS.
  remember (h :: t) as l.
  revert h t Heql.
  induction VDDS as [h1 h2 t'' r | h' t1 t2 VDDS].
  - intros h t [= -> ->].
    clear h r.
    specialize (wf h1).
    revert t; induction wf as [h1 H IH]; intros t.
    constructor; inversion 1; subst.
    + now apply IH.
    + clear IH H0.
      induction H3.
      *
Abort.

Inductive Hydra  {A : Type} (R : A -> A -> Prop) : list A -> list A -> Prop :=
| Hydra_hydra : forall (a : A) (l : list A), Forall (fun x => R x a) l -> Hydra R l [a]
| Hydra_head :
    forall {h1 h2 : A} (t : list A),
      R h1 h2 -> Hydra R (h1 :: t) (h2 :: t)
| Hydra_tail :
    forall (h : A) {t1 t2 : list A},
      Hydra R t1 t2 -> Hydra R (h :: t1) (h :: t2).

End List.

Module BT.

Inductive BT (A : Type) : Type :=
| E : BT A
| N : A -> BT A -> BT A -> BT A.

Arguments E {A}.
Arguments N {A} _ _ _.

Inductive DeepDirectSubterm {A : Type} (R : A -> A -> Prop) : BT A -> BT A -> Prop :=
| DDS_v :
    forall {v1 v2 : A} (l r : BT A),
      R v1 v2 -> DeepDirectSubterm R (N v1 l r) (N v2 l r)
| DDS_l :
    forall (v : A) (l r : BT A),
      DeepDirectSubterm R l (N v l r)
| DDS_r :
    forall (v : A) (l r : BT A),
      DeepDirectSubterm R r (N v l r).

End BT.