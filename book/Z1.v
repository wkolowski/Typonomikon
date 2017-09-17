(** * Z1: Teoria funkcji (alfa, TODO) *)

Require Import Arith.

(** Prerekwizyty:
    - [Empty_set], [unit], [prod], [sum] i funkcje
    - właściwości konstruktorów?
    - [exists!] *)

(** W tym rozdziale zapoznamy się z najważniejszymi rodzajami funkcji.
    Trzeba przyznać na wstępie, że rozdział będzie raczej matematyczny. *)

(** * Injekcje *)

(** TODO ACHTUNG: to pojęcie zostało użyte implicite przy opisywaniu
    właściciwości konstruktorów. *)

Definition injective {A B : Type} (f : A -> B) : Prop :=
  forall x x' : A, f x = f x' -> x = x'.

(** Objaśnienia zacznijmy od nazwy. Po łacinie "iacere" znaczy "rzucać",
    zaś "in" znaczy "w, do". W językach romańskich samo słowo "injekcja"
    oznacza zaś zastrzyk. Bliższym matematycznemu znaczeniu byłoby jednak
    tłumaczenie "wstrzyknięcie". Jeżeli funkcja jest injekcją, to możemy
    też powiedzieć, że jest "injektywna". Inną nazwą jest "funkcja
    różnowartościowa".

    en.wikipedia.org/wiki/Bijection,%%20injection%%20and%%20surjection

    Tutaj można zapoznać się z obrazkami poglądowymi.

    Podstawowa idea jest prosta: jeżeli funkcja jest injekcją, to identyczne
    jej wartości pochodzą od równych argumentów.

    Przekonajmy się na przykładzie. *)

Goal injective (fun n : nat => 2 + n).
Proof.
  unfold injective; intros. destruct x, x'; cbn in *.
    trivial.
    inversion H.
    inversion H.
    inversion H. trivial.
Qed.

(** Funkcja [fun n : nat => 2 + n], czyli dodanie [2] z lewej strony, jest
    injekcją, gdyż jeżeli [2 + n = 2 + n'], to rozwiązując równanie dostajemy
    [n = n']. Jeżeli wartości funkcji są równe, to argumenty również muszą
    być równe.

    Zobaczmy też kontrprzykład. *)

Goal ~ injective (fun n : nat => n * n - n).
Proof.
  unfold injective, not; intros.
  specialize (H 0 1). simpl in H. specialize (H eq_refl). inversion H.
Qed.

(** Funkcja f(n) = n^2 - n nie jest injekcją, gdyż mamy zarówno f(0) = 0
    jak i f(1) = 0. Innymi słowy: są dwa nierówne argumenty (0 i 1), dla
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
    jest ogólniejsza od drugiej. *)

(** **** Ćwiczenie *)

(** Pokaż, że [injective] jest mocniejsze od [injective']. Pokaż też, że w
    logice klasycznej są one równoważne. *)

Theorem injective_injective' :
  forall (A B : Type) (f : A -> B),
    injective f -> injective' f.
(* begin hide *)
Proof.
  unfold injective, injective', not; intros.
  apply H0. apply H. assumption.
Qed.
(* end hide *)

Theorem injective'_injective :
  (forall P : Prop, ~ ~ P -> P) ->
  forall (A B : Type) (f : A -> B),
    injective' f -> injective f.
(* begin hide *)
Proof.
  unfold injective, injective', not; intros.
  apply H. intro. apply (H0 x x'); assumption.
Qed.
(* end hide *)

(** Udowodnij, że różne funkcje są lub nie są injektywne. *)

Theorem id_injective :
  forall A : Type, injective (fun x : A => x).
(* begin hide *)
Proof.
  intro. unfold injective. trivial.
Qed.
(* end hide *)

Theorem S_injective : injective S.
(* begin hide *)
Proof.
  red. inversion 1. trivial.
Qed.
(* end hide *)

Theorem const_unit_inj :
  forall (A : Type) (a : A),
    injective (fun _ : unit => a).
(* begin hide *)
Proof.
  unfold injective; intros. destruct x, x'. trivial.
Qed.
(* end hide *)

Theorem add_k_left_inj :
  forall k : nat, injective (fun n : nat => k + n).
(* begin hide *)
Proof.
  red. induction k as [| k']; simpl; intros.
    assumption.
    inversion H. apply IHk'. assumption.
Qed.
(* end hide *)

Theorem mul_k_inj :
  forall k : nat, k <> 0 -> injective (fun n : nat => k * n).
(* begin hide *)
Proof.
  red. intros k H x x'. generalize dependent k. generalize dependent x'.
  induction x as [| y]; induction x' as [| y']; simpl; intros.
    trivial.
    do 2 (rewrite mult_comm in H0; simpl in *). destruct k.
      contradiction H. trivial.
      simpl in H0. inversion H0.
    rewrite mult_0_r in H0. rewrite mult_comm in H0. simpl in H0. destruct k.
      contradiction H. trivial.
      simpl in H0. inversion H0.
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

Theorem const_2elem_not_inj :
  forall (A B : Type) (b : B),
    (exists a a' : A, a <> a') -> ~ injective (fun _ : A => b).
(* begin hide *)
Proof.
  unfold injective, not; intros. destruct H as [a [a' H]].
  specialize (H0 a a' eq_refl). contradiction.
Qed.
(* end hide *)

Theorem mul_k_0_not_inj :
  ~ injective (fun n : nat => 0 * n).
(* begin hide *)
Proof.
  simpl. apply const_2elem_not_inj. exists 0, 1. inversion 1.
Qed.
(* end hide *)

Theorem pred_not_injective : ~ injective pred.
(* begin hide *)
Proof.
  unfold injective; intro. specialize (H 0 1 eq_refl). inversion H.
Qed.
(* end hide *)

(** Jedną z ważnych właściwości injekcji jest to, że są składalne:
    złożenie dwóch injekcji daje injekcję. *)

Theorem inj_comp :
  forall (A B C : Type) (f : A -> B) (g : B -> C),
    injective f -> injective g -> injective (fun x : A => g (f x)).
(* begin hide *)
Proof.
  unfold injective; intros.
  specialize (H0 _ _ H1). specialize (H _ _ H0). assumption.
Qed.
(* end hide *)

(** Ta właściwość jest dziwna. Być może kiedyś wymyślę dla niej jakąś
    bajkę. *)

Theorem LOLWUT :
  forall (A B C : Type) (f : A -> B) (g : B -> C),
    injective (fun x : A => g (f x)) -> injective f.
(* begin hide *)
Proof.
  unfold injective; intros.
  apply H. rewrite H0. trivial.
Qed.
(* end hide *)

(** Na zakończenie należy dodać do naszej interpretacji pojęcia "injekcja"
    jeszcze jedną ideę. Mianowicie jeżeli istnieje injekcja [f : A -> B],
    to ilość elementów typu [A] jest mniejsza lub równa liczbie elementów
    typu [B], a więc typ [A] jest w pewien sposób mniejszy od [B].

    [f] musi przyporządkować każdemu elementowi [A] jakiś element [B]. Gdy
    elementów [A] jest więcej niż [B], to z konieczności któryś z elementów
    [B] będzie obrazem dwóch lub więcej elementów [A].

    Wobec powyższego stwierdzenie "złożenie injekcji jest injekcją" możemy
    zinterpretować po prostu jako stwierdzenie, że relacja porządku, jaką
    jest istnienie injekcji, jest przechodnia. (TODO: to wymagałoby relacji
    jako prerekwizytu). *)

(** **** Ćwiczenie *)

(** Udowodnij, że nie istnieje injekcja z [bool] w [unit]. Znaczy to, że
    [bool] ma więcej elementów, czyli jest większy, niż [unit]. *)

Theorem no_inj_bool_unit :
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

Theorem inj_Empty_set_A :
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

Theorem pred_surjective : surjective pred.
Proof.
  unfold surjective; intros. exists (S b). cbn. trivial.
Qed.

(** TODO Uwaga techniczna: od teraz do upraszczania zamiast taktyki [simpl]
    używać będziemy taktyki [cbn]. Różni się ona nieznacznie od [simpl], ale
    jej główną zaletą jest nazwa — [cbn] to trzy litery, a [simpl] aż pięć,
    więc zaoszczędzimy sobie pisania.

    Powyższe twierdzenie głosi, że "funkcja [pred] jest surjekcją", czyli,
    parafrazując, "każda liczba naturalna jest poprzednikiem innej liczby
    naturalnej". Nie powinno nas to zaskakiwać, wszakże każda liczba naturalna
    jest poprzednikiem swojego następnika, tzn. [pred (S n) = n]. *)

Theorem S_not_surjective : ~ surjective S.
Proof.
  unfold surjective; intro. destruct (H 0). inversion H0.
Qed.

(** Surjekcją nie jest za to konstruktor [S]. To również nie powinno nas
    dziwić: istnieje przecież liczba naturalna, która nie jest następnikiem
    żadnej innej. Jest nią oczywiście zero.

    Surjekcje cieszą się właściwościami podobnymi do tych, jakie są udziałem
    injekcji. *)

(** **** Ćwiczenie *)

(** Pokaż, że złożenie surjekcji jest surjekcją. Udowodnij też "dziwną
    właściwość" surjekcji. *)

Theorem sur_comp :
  forall (A B C : Type) (f : A -> B) (g : B -> C),
    surjective f -> surjective g -> surjective (fun x : A => g (f x)).
(* begin hide *)
Proof.
  unfold surjective; intros A B C f g Hf Hg c.
  destruct (Hg c) as [b Heq]. destruct (Hf b) as [a Heq'].
  subst. exists a. trivial.
Qed.
(* end hide *)

Theorem LOLWUT_sur :
  forall (A B C : Type) (f : A -> B) (g : B -> C),
    surjective (fun x : A => g (f x)) -> surjective g.
(* begin hide *)
Proof.
  unfold surjective; intros A B C f g Hgf c.
  destruct (Hgf c) as [a Heq]. subst. exists (f a). trivial.
Qed.
(* end hide *)

(** **** Ćwiczenie *)

(** Zbadaj, czy wymienione funkcje są surjekcjami. Sformułuj i udowodnij
    odpowiednie twierdzenia.

    Funkcje: identyczność, dodawanie (rozważ zero osobno), odejmowanie,
    mnożenie (rozważ 1 osobno). *)

(* begin hide *)
Theorem id_sur :
  forall A : Type, surjective (fun x : A => x).
Proof.
  red; intros. exists b. trivial.
Qed.

Theorem plus_0_l_sur : surjective (fun n : nat => 0 + n).
Proof.
  red; intros. exists b. trivial.
Qed.

Theorem plus_0_r_sur : surjective (fun n : nat => n + 0).
Proof.
  red; intros. exists b. rewrite <- plus_n_O. trivial.
Qed.

Theorem plus_Sn_l_not_sur :
  forall k : nat, ~ surjective (fun n : nat => S k + n).
Proof.
  unfold surjective, not; intros. specialize (H 0).
  destruct H as [a H]. inversion H.
Qed.

Theorem plus_Sn_r_not_sur :
  forall k : nat, ~ surjective (fun n : nat => n + S k).
Proof.
  unfold surjective, not; intros. specialize (H 0).
  destruct H as [a H]. rewrite plus_comm in H. inversion H.
Qed.

Theorem minus_sur :
  forall k : nat, surjective (fun n : nat => n - k).
Proof.
  red; intros. exists (k + b). rewrite minus_plus. trivial.
Qed.

Theorem mult_1_l_sur : surjective (fun n : nat => 1 * n).
Proof.
  red; intros. exists b. Search (1 * _). apply Nat.mul_1_l.
Qed.

Theorem mult_1_r_sur : surjective (fun n : nat => n * 1).
Proof.
  red; intros. exists b. apply Nat.mul_1_r.
Qed.

Theorem mult_0_l_not_sur : ~ surjective (fun n : nat => 0 * n).
Proof.
  unfold surjective, not; intros. specialize (H 1).
  destruct H as [a H]. simpl in H. inversion H.
Qed.

Theorem mult_0_r_not_sur : ~ surjective (fun n : nat => n * 0).
Proof.
  unfold surjective, not; intros. specialize (H 1).
  destruct H as [a H]. rewrite Nat.mul_0_r in H. inversion H.
Qed.

Theorem mult_SS_l_not_sur :
  forall k : nat, ~ surjective (fun n : nat => S (S k) * n).
Proof.
  unfold surjective, not; intros. specialize (H 1).
  destruct H as [a H]. destruct a as [| a']; simpl in H.
    rewrite Nat.mul_0_r in H. inversion H.
    inversion H. rewrite plus_comm in H1. inversion H1.
Qed.

Theorem mult_SS_r_not_sur :
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
    surjekcją możemy traktować jako stwierdzenie, że porządek, jakim jest
    istnienie surjekcji, jest przechodni. (TODO) *)

(** **** Ćwiczenie *)

(** Pokaż, że nie istnieje surjekcja z [unit] w [bool]. Oznacza to, że [unit]
    nie jest większy niż [bool]. *)

Theorem no_sur_unit_bool :
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

Theorem sur_A_unit :
  forall (A : Type) (nonempty : A), exists f : A -> unit, surjective f.
(* begin hide *)
Proof.
  unfold surjective; intros. exists (fun _ => tt).
  destruct b. exists nonempty. trivial.
Qed.
(* end hide *)

(** * Bijekcje *)

Definition bijective {A B : Type} (f : A -> B) : Prop :=
  injective f /\ surjective f.

(** Po łacinie przedrostek "bi-" oznacza "dwa". Bijekcja to funkcja, która
    jest zarówno injekcją, jak i surjekcją. *)

Theorem id_bij : forall A : Type, bijective (fun x : A => x).
Proof.
  split; intros.
    apply id_injective.
    apply id_sur.
Qed.

Theorem S_not_bij : ~ bijective S.
Proof.
  unfold bijective; intro. destruct H.
  apply S_not_surjective. assumption.
Qed.

(** Pozostawię przykłady bez komentarza — są one po prostu konsekwencją tego,
    co już wiesz na temat injekcji i surjekcji.

    Ponieważ bijekcja jest surjekcją, to każdy element jej przeciwdziedziny
    jest obrazem jakiegoś elementu jej dziedziny (obraz elementu [x] to po
    prostu [f x]). Ponieważ jest injekcją, to element ten jest unikalny.

    Bijekcja jest więc taką funkcją, że każdy element jej przeciwdziedziny
    jest obrazem dokładnie jednego elementu jej dziedziny. Ten właśnie fakt
    wyraża poniższa definicja alternatywna.

    TODO: [exists!] nie zostało dotychczas opisane, a chyba nie powinno być
    opisane tutaj. *)

Definition bijective' {A B : Type} (f : A -> B) : Prop :=
  forall b : B, exists! a : A, f a = b.

(** **** Ćwiczenie *)

(** Udowodnij, że obie definicje są równoważne. *)

Theorem bijective_bijective' :
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

Require Import List.
Import ListNotations.

Fixpoint unary (n : nat) : list unit :=
match n with
    | 0 => []
    | S n' => tt :: unary n'
end.

(** Funkcja [unary] reprezentuje liczbę naturalną [n] za pomocą listy
    zawierającej [n] kopii termu [tt]. Udowodnij, że [unary] jest
    bijekcją. *)

Theorem unary_bij : bijective unary.
(* begin hide *)
Proof.
  unfold bijective, injective, surjective. split.
    induction x as [| y]; induction x' as [| y']; simpl in *.
      trivial.
      inversion 1.
      inversion 1.
      inversion 1. f_equal. apply IHy. assumption.
    intro. exists (length b). induction b as [| h t]; simpl.
      trivial.
      destruct h. f_equal. assumption.
Qed.
(* end hide *)

(** Jak już powiedzieliśmy, bijekcje dziedziczą właściwości, które mają
    zarówno injekcje, jak i surjekcje. Wobec tego możemy skonkludować,
    że złożenie bijekcji jest bijekcją. Nie mają one jednak "dziwnej
    własciwości".

    TODO UWAGA: od teraz twierdzenia, które pozostawię bez dowodu, z
    automatu stają się ćwiczeniami. *)

Theorem bij_comp :
  forall (A B C : Type) (f : A -> B) (g : B -> C),
    bijective f -> bijective g -> bijective (fun x : A => g (f x)).
(* begin hide *)
Proof.
  unfold bijective; intros. destruct H, H0. split.
    apply inj_comp; assumption.
    apply sur_comp; assumption.
Qed.
(* end hide *)

(** Bijekcje mają też interpretacje w idei rozmiaru oraz ilości elementów.
    Jeżeli istnieje bijekcja [f : A -> B], to znaczy, że typy [A] oraz [B]
    mają dokładnie tyle samo elementów, czyli są "tak samo duże".

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
    relacją równoważności. TODO: prerekwizyt: relacje równoważności *)

Definition equipotent (A B : Type) : Prop :=
  exists f : A -> B, bijective f.

Notation "A ~ B" := (equipotent A B) (at level 40).

(** Równoliczność [A] i [B] będziemy oznaczać przez [A ~ B]. Nie należy
    notacji [~] mylić z notacją [~] oznaczającej negację logiczną. Ciężko
    jednak jest je pomylić, gdyż pierwsza zawsze bierze dwa argumenty, a
    druga tylko jeden. *)

Theorem equipotent_refl :
  forall A : Type, A ~ A.
(* begin hide *)
Proof.
  red. intro. exists (fun x : A => x). apply id_bij.
Qed.
(* end hide *)

Theorem equipotent_sym :
  forall A B : Type, A ~ B -> B ~ A.
(* begin hide *)
Proof.
  unfold equipotent, bijective; intros. destruct H as [f [Hinj Hsur]].
  red in Hsur. assert (B -> A).
    intro b. Fail destruct (Hsur b) as [a H].
Admitted.
(* end hide *)

Theorem equipotent_trans :
  forall A B C : Type, A ~ B -> B ~ C -> A ~ C.
(* begin hide *)
Proof.
  unfold equipotent; intros. destruct H as [f Hf], H0 as [g Hg].
  exists (fun x : A => g (f x)). apply bij_comp; assumption.
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
    odwrotnością. Spotkaliśmy się już z przykładami inwolucji: najbardziej
    trywialnym z nich jest funkcja identycznościowa, bardziej oświecającym
    zaś funkcja [rev], która odwraca listę — odwrócenie listy dwukrotnie
    daje wyjściową listę. Inwolucją jest też [negb]. *)

Theorem id_inv :
  forall A : Type, involutive (fun x : A => x).
(* begin hide *)
Proof.
  red; intros. trivial.
Qed.
(* end hide *)

Theorem rev_inv :
  forall A : Type, involutive (@rev A).
(* begin hide *)
Proof.
  red; intros. apply rev_involutive.
Qed.
(* end hide *)

Theorem negb_inv : involutive negb.
(* begin hide *)
Proof.
  red. destruct x; cbn; trivial.
Qed.
(* end hide *)

(** Ponieważ każda inwolucja ma odwrotność (którą jest ona sama), każda
    inwolucja jest z automatu bijekcją. *)

Theorem inv_bij :
  forall (A : Type) (f : A -> A), involutive f -> bijective f.
(* begin hide *)
Proof.
  unfold involutive, bijective; intros. split; red; intros.
    rewrite <- (H x), <- (H x'). rewrite H0. trivial.
    exists (f b). apply H.
Qed.
(* end hide *)

(* begin hide *)
Function count_inv (n : nat) : nat :=
match n with
    | 0 => 1
    | 1 => 1
    | S ((S n'') as n') => count_inv n' + (n - 1) * count_inv n''
end.

Compute count_inv 6.
Compute map count_inv [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11].
(* end hide *)


