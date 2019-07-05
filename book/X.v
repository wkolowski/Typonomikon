(** * X: Chilowo śmietnik *)

(** * Parametryczność *)

(** UWAGA TODO: ten podrozdział zawiera do pewnego stopnia kłamstwa (tzn.
    dość uproszczony punkt widzenia). *)

(** Niech [A B : Set]. Zadajmy sobie następujące pytanie: ile jest funkcji
    typu [A -> B]? Żeby ułatwić sobie zadanie, ograniczmy się jedynie do
    typów, które mają skończoną ilość elementów.

    Nietrudno przekonać się, że ich ilość to |B|^|A|, gdzie ^ oznacza
    potęgowanie, zaś |T| to ilość elementów typu [T] (ta notacja nie ma
    nic wspólnego z Coqiem — zaadaptowałem ją z teorii zbiorów jedynie
    na potrzeby tego podrozdziału).

    Udowodnić ten fakt możesz (choć póki co nie w Coqu) posługując się
    indukcją po ilości elementów typu [A]. Jeżeli [A] jest pusty, to
    jest tylko jedna taka funkcja, o czym przekonałeś się już podczas
    ćwiczeń w podrozdziale o typie [Empty_set]. *)

(** **** Ćwiczenie *)

(** Udowodnij (nieformalnie, na papierze), że w powyższym akapicie nie
    okłamałem cię. *)

(** **** Ćwiczenie *)

(** Zdefiniuj wszystkie możliwe funkcje typu [unit -> unit], [unit -> bool]
    i [bool -> bool]. *)

(** Postawmy sobie teraz trudniejsze pytanie: ile jest funkcji typu
    [forall A : Set, A -> A]? W udzieleniu odpowiedzi pomoże nam
    parametryczność — jedna z właściwości Coqowego polimorfizmu.

    Stwierdzenie, że polimorfizm w Coqu jest parametryczny, oznacza, że
    funkcja biorąca typ jako jeden z argumentów działa w taki sam sposób
    niezależnie od tego, jaki typ przekażemy jej jako argument.

    Konsekwencją tego jest, że funkcje polimorficzne nie wiedzą (i nie
    mogą wiedzieć), na wartościach jakiego typu operują. Wobec tego
    elementem typu [forall A : Set, A -> A] nie może być funkcja, która
    np. dla typu [nat] stale zwraca [42], a dla innych typów po prostu
    zwraca przekazany jej argument.

    Stąd konkludujemy, że typ [forall A : Set, A -> A] ma tylko jeden
    element, a mianowicie polimorficzną funkcję identycznościową. *)

Definition id' : forall A : Set, A -> A :=
  fun (A : Set) (x : A) => x.

(** **** Ćwiczenie *)

(** Zdefiniuj wszystkie elementy następujących typów lub udowodnij, że
    istnienie choć jednego elementu prowadzi do sprzeczności:
    - [forall A : Set, A -> A -> A]
    - [forall A : Set, A -> A -> A -> A]
    - [forall A B : Set, A -> B]
    - [forall A B : Set, A -> B -> A]
    - [forall A B : Set, A -> B -> B]
    - [forall A B : Set, A -> B -> A * B]
    - [forall A B : Set, A -> B -> sum A B]
    - [forall A B C : Set, A -> B -> C]
    - [forall A : Set, option A -> A]
    - [forall A : Set, list A -> A] *)

(* begin hide *)
Theorem no_such_fun :
  (forall A B : Set, A -> B) -> False.
Proof.
  intros. exact (X nat False 42).
Qed.
(* end hide *)

(** TODO: tu opisać kłamstwo *)

Inductive path {A : Type} (x : A) : A -> Type :=
    | idpath : path x x.

Arguments idpath {A} _.

Axiom LEM : forall (A : Type), A + (A -> Empty_set).

Open Scope type_scope.

Definition bad' (A : Type) :
  {f : A -> A &
    (@path Type bool A * forall x : A, f x <> x) +
    ((@path Type bool A -> Empty_set) * forall x : A, f x = x)}.
Proof.
  destruct (LEM (@path Type bool A)).
    destruct p. esplit with negb. left. split.
      exact (@idpath Type bool).
      destruct x; cbn; inversion 1.
    esplit with (fun x : A => x). right. split.
      assumption.
      reflexivity.
Defined.

Definition bad (A : Type) : A -> A := projT1 (bad' A).

Lemma bad_is_bad :
  forall b : bool, bad bool b <> b.
Proof.
  intros. unfold bad. destruct bad'. cbn. destruct s as [[p H] | [p H]].
    apply H.
    destruct (p (idpath _)).
Defined.

Lemma bad_ist_gut :
  forall (A : Type) (x : A),
    (@path Type bool A -> Empty_set) -> bad A x = x.
Proof.
  unfold bad. intros A x p. destruct bad' as [f [[q H] | [q H]]]; cbn.
    destruct (p q).
    apply H.
Defined.

(** * Rozstrzygalność *)

Theorem excluded_middle :
  forall P : Prop, P \/ ~ P.
Proof.
  intro. left.
Restart.
  intro. right. intro.
Abort.

(** Próba udowodnienia tego twierdzenia pokazuje nam zasadniczą różnicę
    między logiką konstruktywną, która jest domyślną logiką Coqa, oraz
    logiką klasyczną, najpowszechniej znanym i używanym rodzajem logiki.

    Każde zdanie jest, w pewnym "filozoficznym" sensie, prawdziwe lub
    fałszywe i to właśnie powyższe zdanie oznacza w logice klasycznej.
    Logika konstruktywna jednak, jak już wiemy, nie jest logiką prawdy,
    lecz logiką udowadnialności i ma swoją interpretację obliczeniową.
    Powyższe zdanie w logice konstruktywnej oznacza: program komputerowy
    [exluded_middle] rozstrzyga, czy dowolne zdanie jest prawdziwe, czy
    fałszywe.

    Skonstruowanie programu o takim typie jest w ogólności niemożliwe,
    gdyż dysponujemy zbyt małą ilością informacji: nie wiemy czym jest
    zdanie [P], a nie posiadamy żadnego ogólnego sposobu dowodzenia lub
    obalania zdań o nieznanej nam postaci. Nie możemy np. użyć indukcji,
    gdyż nie wiemy, czy zdanie [P] zostało zdefiniowane induktywnie, czy
    też nie. W Coqu jedynym sposobem uzyskania termu o typie [forall
    P : Prop, P \/ ~ P] jest przyjęcie go jako aksjomat. *)

Theorem True_dec : True \/ ~ True.
Proof.
  left. trivial.
Qed.

(** Powyższe dywagacje nie przeszkadzają nam jednak w udowadnianiu,
    że reguła wyłączonego środka zachodzi dla pewnych konkretnych
    zdań. Zdanie takie będziemy nazywać zdaniami rozstrzygalnymi
    (ang. decidable). O pozostałych zdaniach będziemy mówić, że są 
    nierozstrzygalne (ang. undecidable). Ponieważ w Coqu wszystkie
    funkcje są rekurencyjne, a dowody to programy, to możemy powyższą
    definicję rozumieć tak: zdanie jest rozstrzygalne, jeżeli istnieje
    funkcja rekurencyjna o przeciwdzidzinie [bool], która sprawdza, czy
    jest ono prawdziwe, czy fałszywe.

    Przykładami zdań, predykatów czy problemów rozstrzygalnych są:
    - sprawdzanie, czy lista jest niepusta
    - sprawdzanie, czy liczba naturalna jest parzysta
    - sprawdzanie, czy dwie liczby naturalne są równe *)

(** Przykładem problemów nierozstrzygalnych są:
    - dla funkcji [f g : nat -> nat] sprawdzenie, czy
      [forall n : nat, f n = g n] — jest to w ogólności niemożliwe,
      gdyż wymaga wykonania nieskończonej ilości porównań (co nie
      znaczy, że nie da się rozwiązać tego problemu dla niektórych
      funkcji)
    - sprawdzenie, czy słowo o nieskończonej długości jest palindromem *)

(** **** Ćwiczenie *)

Theorem eq_nat_dec :
  forall n m : nat, n = m \/ ~ n = m.
(* begin hide *)
Proof.
  induction n as [| n']; destruct m as [| m'].
    left. trivial.
    right. inversion 1.
    right. inversion 1.
    destruct (IHn' m').
      left. subst. trivial.
      right. intro. inversion H0. subst. contradiction H. trivial.
Qed.
(* end hide *)

(** ** Techniczne apekty rozstrzygalności *)

(** Podsumowując powyższe rozważania, moglibyśmy stwierdzić: zdanie [P] jest
    rozstrzygalne, jeżeli istnieje term typu [P \/ ~ P]. Stwierdzenie takie
    nie zamyka jednak sprawy, gdyż bywa czasem mocno bezużyteczne.

    Żeby to zobrazować, spróbujmy użyć twierdzenia [eq_nat_dec] do napisania
    funkcji, która sprawdza, czy liczna naturalna [n] występuje na liście
    liczb naturalnych [l]: *)

Fail Fixpoint inb_nat (n : nat) (l : list nat) : bool :=
match l with
    | nil => false
    | cons h t =>
        match eq_nat_dec n h with
            | or_introl _ => true
            | _ => inb_nat n t
        end
end.

(** Coq nie akceptuje powyższego kodu, racząc nas informacją o błędzie: *)

(* Error:
   Incorrect elimination of "eq_nat_dec n h0" in the inductive type "or":
   the return type has sort "Set" while it should be "Prop".
   Elimination of an inductive object of sort Prop
   is not allowed on a predicate in sort Set
   because proofs can be eliminated only to build proofs. *)

(** Nasza porażka wynika z faktu, że do zdefiniowania funkcji, która
    jest programem (jej dziedzina i przeciwdziedzina są sortu [Set])
    próbowaliśmy użyć termu [eq_nat_dec n h], który jest dowodem
    (konkluzją [eq_nat_dec] jest równość, która jest sortu [Prop]).

    Mimo korespondencji Curry'ego-Howarda, która odpowiada za olbrzymie
    podobieństwo specyfikacji i zdań, programów i dowodów, sortu [Set]
    i sortu [Prop], są one rozróżniane i niesie to za sobą konsekwencje:
    podczas gdy programów możemy używać wszędzie, dowodów możemy używać
    jedynie do konstruowania innych dowodów.

    Praktycznie oznacza to, że mimo iż równość liczb naturalnych jest
    rozstrzygalna, pisząc program nie mamy możliwości jej rozstrzygania
    za pomocą [eq_nat_dec]. To właśnie miałem na myśli pisząc, że termy
    typu [P \/ ~ P] są mocno bezużyteczne.

    Uszy do góry: nie wszystko stracone! Jest to tylko drobna przeszkoda,
    którą bardzo łatwo ominąć: *)

Inductive sumbool (A B : Prop) : Set :=
    | left : A -> sumbool A B
    | right : B -> sumbool A B.

(** Typ [sumbool] jest niemal dokładną kopią [or], jednak nie żyje on
    w [Prop], lecz w [Set]. Ta drobna sztuczka, że termy typu
    [sumbool A B] formalnie są programami, mimo że ich naturalna
    interpretacja jest taka sama jak [or], a więc jako dowodu
    dysjunkcji. *)

(** **** Ćwiczenie *)

(** Udowodnij twierdzenie [eq_nat_dec'] o rozstrzygalności [=] na
    liczbach naturalnych. Użyj typu [sumbool]. Następnie napisz
    funkcję [inb_nat], która sprawdza, czy liczba naturalna [n]
    jest obecna na liście [l]. *)

(** * Typy hybrydowe *)

(** Ostatnim z typów istotnych z punktu widzenia silnych specyfikacji
    jest typ o wdzięcznej nazwie [sumor]. *)

Module sumor.

Inductive sumor (A : Type) (B : Prop) : Type :=
    | inleft : A -> sumor A B
    | inright : B -> sumor A B.

(** Jak sama nazwa wskazuje, [sumor] jest hybrydą sumy rozłącznej [sum]
    oraz dysjunkcji [or]. Możemy go interpretować jako typ, którego
    elementami są elementy [A] albo wymówki w stylu "nie mam elementu [A],
    ponieważ zachodzi zdanie [B]". [B] nie zależy od [A], a więc jest to
    zwykła suma (a nie suma zależna, czyli uogólnienie produktu). [sumor]
    żyje w [Type], a więc jest to specyfikacja i liczy się konkretna
    postać jego termów, a nie jedynie fakt ich istnienia. *)

(** **** Ćwiczenie ([pred']) *)

(** Zdefiniuj funkcję [pred'], która przypisuje liczbie naturalnej jej
    poprzednik. Poprzednikiem [0] nie powinno być [0]. Mogą przydać ci
    się typ [sumor] oraz sposób definiowania za pomocą taktyk, omówiony
    w podrozdziale dotyczącym sum zależnych. *)

(* begin hide *)
Definition pred' (n : nat) : sumor nat (n = 0) :=
match n with
    | 0 => inright _ _ eq_refl
    | S n' => inleft _ _ n'
end.
(* end hide *)

End sumor.