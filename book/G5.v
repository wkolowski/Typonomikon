(** * G5: Indukcja-rekursja *)

Require Import List.
Import ListNotations.

Require Import Arith Lia.

From Typonomikon Require Import D2g.

(** * Wstęp (TODO) *)

Module ind_rec.

(** A oto kolejny potfur do naszej kolekcji: indukcja-rekursja. Nazwa, choć
    brzmi tak głupio, jak "indukcja-indukcja", niesie ze sobą jednak dużo
    więcej wyobraźni: indukcja-rekursja pozwala nam jednocześnie definiować
    typy induktywne oraz operujące na nich funkcje rekurencyjne.

    Co to dokładnie znaczy? Dotychczas nasz modus operandi wyglądał tak, że
    najpierw definiowaliśmy jakiś typ induktywny, a potem przez rekursję
    definiowaliśmy operujące na nim funkcje, np:
    - najpierw zdefiniowaliśmy typ [nat], a potem dodawanie, mnożenie etc.
    - najpierw zdefiniowaliśmy typ [list A], a potem [app], [rev] etc. *)

(** Dlaczego mielibyśmy chcieć definiować typ i funkcję jednocześnie? Dla
    tego samego, co zawsze, czyli zależności - indukcja-rekursja pozwala,
    żeby definicja typu odnosiła się do funkcji, która to z kolei jest
    zdefiniowana przez rekursję strukturalną po argumencie o tym typie.

    Zobaczmy dobrze nam już znany bezsensowny przykład, czyli listy
    posortowane, tym razem zaimplementowane za pomocą indukcji-rekursji. *)

(** * Listy posortowane, znowu (TODO) *)

(*
Inductive slist {A : Type} (R : A -> A -> bool) : Type :=
| snil : slist R
| scons : forall (h : A) (t : slist R), ok h t = true -> slist R

with

Definition ok
  {A : Type} {R : A -> A -> bool} (x : A) (t : slist R) : bool :=
match t with
| snil => true
| scons h _ _ => R x h
end.
*)

(** Coq niestety nie wspiera indukcji-rekursji, a próba napisania powyższej
    definicji kończy się błędem składni, przy którym nie pomaga nawet komenda
    [Fail]. Podobnie jak poprzednio, pomożemy sobie za pomocą aksjomatów,
    jednak najpierw prześledźmy definicję.

    Typ [slist R] działa następująco:
    - [R] to jakiś porządek. Zauważ, że tym razem [R : A -> A -> bool], a
      więc porządek jest reprezentowany przez funkcję, która go rozstrzyga
    - [snil] to lista pusta
    - [scons h t p] to lista z głową [h] i ogonem [t], zaś [p : ok h t = true]
      to dowód na to, że dostawienie [h] przed [t] daje listę posortowaną. *)

(** Tym razem jednak [ok] nie jest relacją, lecz funkcją zwracającą [bool],
    która działa następująco:
    - dla [snil] zwróć [true] - każde [x : A] można dostawić do listy pustej
    - dla [scons h _ _] zwróć wynik porównania [x] z [h] *)

(** Istotą mechanizmu indukcji-rekursji w tym przykładzie jest to, że [scons]
    wymaga dowodu na to, że funkcja [ok] zwraca [true], podczas gdy funkcja
    ta jest zdefiniowana przez rekursję strukturalną po argumencie typu
    [slist R].

    Użycie indukkcji-rekursji do zaimplementowania [slist] ma swoje zalety:
    dla konkretnych list (złożonych ze stałych, a nie ze zmiennych) dowody
    [ok h t = true] będą postaci [eq_refl], bo [ok] po prostu obliczy się
    do [true]. W przypadku indukcji-indukcji dowody na [ok h t] były całkiem
    sporych rozmiarów drzewami. Innymi słowy, udało nam się zastąpić część
    termu obliczeniami. Ten intrygujący motyw jeszcze się w przyszłości
    pojawi, gdy omawiać będziemy dowód przez reflekcję.

    Dosyć gadania! Zobaczmy, jak zakodować powyższą definicję za pomocą
    aksjomatów. *)

Axioms
  (slist : forall {A : Type}, (A -> A -> bool) -> Type)
  (ok :
    forall {A : Type} {R : A -> A -> bool}, A -> slist R -> bool)
  (snil :
    forall {A : Type} {R : A -> A -> bool}, slist R)
  (scons :
    forall
      {A : Type} {R : A -> A -> bool}
      (h : A) (t : slist R),
        ok h t = true -> slist R)
  (ok_snil :
    forall {A : Type} {R : A -> A -> bool} (x : A),
      ok x (@snil _ R) = true)
  (ok_scons :
    forall
      {A : Type} {R : A -> A -> bool}
      (x h : A) (t : slist R) (p : ok h t = true),
        ok x (scons h t p) = R x h).

(** Najpierw musimy zadeklarować [slist], a następnie [ok], gdyż typ [ok]
    zależy od [slist]. Następnym krokiem jest zadeklarowanie konstruktorów
    [slist], a później równań definiujących funkcję [ok] - koniecznie w tej
    kolejności, gdyż równania zależą od konstruktorów.

    Jak widać, aksjomaty są bardzo proste i sprowadzają się do przepisania
    powyższej definicji odrzuconej przez Coqa. *)

Axiom
  ind : forall
    (A : Type) (R : A -> A -> bool)
    (P : slist R -> Type)
    (Psnil : P snil)
    (Pscons :
      forall (h : A) (t : slist R) (p : ok h t = true),
        P t -> P (scons h t p)),
    {f : forall l : slist R, P l |
      f snil = Psnil /\
      (forall (h : A) (t : slist R) (p : ok h t = true),
        f (scons h t p) = Pscons h t p (f t))}.

(** Innym zyskiem z użycia indukcji-rekursji jest postać reguły indukcyjnej.
    Jest ona dużo prostsza, niż w przypadku indukcji-indukcji, gdyż teraz
    definiujemy tylko jeden typ, zaś towarzysząca mu funkcja nie wymaga w
    regule niczego specjalnego - po prostu pojawia się w niej tam, gdzie
    spodziewamy się jej po definicji [slist], ale nie robi niczego
    ponad to. Może to sugerować, że zamiast indukcji-indukcji, o ile to
    możliwe, lepiej jest używać indukcji-rekursji, a predykaty i relacje
    definiować przez rekursję.

    Powyższą regułę możemy odczytać następująco:
    - [A : Type] i [R : A -> A -> bool] to parametry [slist], więc muszą się
      pojawić
    - [P : slist R -> Type] to przeciwdziedzina funkcji definiowanej za
      pomocą reguły
    - [Psnil] to wynik funkcji dla [snil]
    - [Pscons] produkuje wynik funkcji dla [scons h t p] z hipotezy
      indukcyjnej/wywołania rekurencyjnego dla [t]
    - [f : forall l : slist R, P l] to funkcja zdefiniowana przez regułę,
      zaś równania formalizują to, co zostało napisane powyżej o [Psnil]
      i [Pscons] *)

(** Termy induktywno-rekurencyjnego [slist R] wyglądają następująco
    (najpierw definiujemy sobie funkcję rozstrzygającą standardowy
    porządek na liczbach naturalnych): *)

Fixpoint leb (n m : nat) : bool :=
match n, m with
| 0, _ => true
| _, 0 => false
| S n', S m' => leb n' m'
end.

Definition slist_01 : slist leb :=
  scons 0
    (scons 1
      snil
      (ok_snil 1))
    (ok_scons 0 1 snil (ok_snil 1)).

(** Nie wygląda wiele lepiej od poprzedniej, induktywno-induktywnej wersji,
    prawda? Ta rażąca kiepskość nie jest jednak zasługą indukcji-rekursji,
    lecz kodowania za pomocą aksjomatów - funkcja [ok] się nie oblicza,
    więc zamiast [eq_refl] musimy używać aksjomatów [ok_snil] i [ok_scons].

    W tym momencie znów wkracza ława oburzonych i wyraża swoje oburzenie na
    fakt, że Coq nie wspiera indukcji-rekursji (ale Agda już tak). Gdyby
    [Coq] wspierał indukcję-rekursję, to ten term wyglądałby tak: *)

Fail Definition slist_01 : slist leb :=
  scons 0 (scons 1 snil eq_refl) eq_refl.

(** Dużo lepiej, prawda? Na koniec zobaczmy, jak zdefiniować funkcję
    zapominającą o fakcie, że lista jest posortowana. *)

Definition toList'
  {A : Type} {R : A -> A -> bool} :
  {f : slist R -> list A |
    f snil = [] /\
    forall (h : A) (t : slist R) (p : ok h t = true),
      f (scons h t p) = h :: f t
  }.
Proof.
  exact (ind A R (fun _ => list A) [] (fun h _ _ r => h :: r)).
Defined.

Definition toList
  {A : Type} {R : A -> A -> bool} : slist R -> list A :=
    proj1_sig toList'.

(** Ponownie jest to dużo prostsze, niż w przypadku indukcji-indukcji -
    wprawdzie wciąż musimy ręcznie wpisywać termy do reguły indukcji,
    ale dzięki prostocie reguły jest to znacznie łatwiejsze. Alternatywnie:
    udało nam się zaoszczędzić trochę czasu na definiowaniu reguły rekursji,
    co w przypadku indukcji-indukcji było niemal konieczne, żeby nie
    zwariować. *)

Lemma toList_slist_01_result :
  toList slist_01 = [0; 1].
Proof.
  unfold toList, slist_01.
  destruct toList' as (f & H1 & H2).
  cbn. rewrite 2!H2, H1. reflexivity.
Qed.

(** Udowodnienie, że nasza funkcja daje taki wynik jak chcieliśmy, jest
    równie proste jak poprzednio. *)

(** **** Ćwiczenie *)

(** Zdefiniuj dla list posortowanych funkcję [slen], która liczy ich długość.
    Udowodnij oczywiste twierdzenie wiążące ze sobą [slen], [toList] oraz
    [length]. Czy było łatwiej, niż w przypadku indukcji-indukcji? *)

(* begin hide *)

Definition slen'
  {A : Type} {R : A -> A -> bool} :
  {f : slist R -> nat |
    f snil = 0 /\
    forall (h : A) (t : slist R) (p : ok h t = true),
      f (scons h t p) = S (f t)}.
Proof.
  exact (ind A R (fun _ => nat) 0 (fun _ _ _ n => S n)).
Defined.

Definition slen {A : Type} {R : A -> A -> bool} : slist R -> nat :=
  proj1_sig slen'.

Lemma slen_toList_length :
  forall {A : Type} {R : A -> A -> bool} (l : slist R),
    slen l = length (toList l).
Proof.
  intros A R.
  eapply (proj1_sig
    (ind A R (fun l : slist R => slen l = length (toList l)) _ _)).
  Unshelve.
  all: cbn; unfold slen, toList;
  destruct slen' as (f & Hf1 & Hf2), toList' as (g & Hg1 & Hg2); cbn.
    rewrite Hf1, Hg1. cbn. reflexivity.
    intros. rewrite Hf2, Hg2, H. cbn. reflexivity.
Qed.

(** Czy było łatwiej, niż zrobić to samo indukcją-indukcją? Tak, ale tylko
    troszkę. *)

(* end hide *)

End ind_rec.

(** * Sterty binarne (TODO) *)

(** **** Ćwiczenie *)

(** No cóż, jeszcze raz to samo. Zdefiniuj za pomocą indukcji-rekursji
    jednocześnie typ stert binarnych [BHeap R], gdzie [R : A -> A -> bool]
    rozstrzyga porządek, i funkcję [ok : A -> BHeap R -> bool], gdzie
    [ok x h = true], gdy stertę [h] można podczepić pod element [x].

    Najpierw napisz pseudodefinicję, a potem przetłumacz ją na odpowiedni
    zestaw aksjomatów.

    Następnie użyj swojej aksjomatycznej definicji, aby zdefiniować funkcję
    [mirror], która tworzy lustrzane odbicie sterty [h : BHeap R]. Wskazówka:
    tym razem powinno ci się udać.

    Porównaj induktywno-rekurencyjną implementację [BHeap R] i [ok] z
    implementacją przez indukcję-indukcję. Która jest bardziej ogólna?
    Która jest "lżejsza"? Która jest lepsza? *)

(* begin hide *)
Module BHeap'.

(*
Inductive BHeap {A : Type} (R : A -> A -> bool) : Type :=
| E : BHeap R
| N : forall (v : A) (l r : BHeap R),
        ok R v l = true -> ok R v r = true -> BHeap R

with ok {A : Type} (R : A -> A -> bool) (x : A) (h : BHeap R) : bool :=
match h with
| E => true
| N v l r _ _ => R x v
end.
*)

Axioms
  (BHeap : forall {A : Type} (R : A -> A -> bool), Type)
  (ok : forall {A : Type} (R : A -> A -> bool) (x : A) (h : BHeap R), bool)
  (E : forall {A : Type} {R : A -> A -> bool}, BHeap R)
  (N :
    forall {A : Type} {R : A -> A -> bool} (v : A) (l r : BHeap R),
      ok R v l = true -> ok R v r = true -> BHeap R)
  (ok_E :
    forall {A : Type} {R : A -> A -> bool} (x : A),
      ok R x E = true)
  (ok_N :
    forall
      {A : Type} {R : A -> A -> bool}
      (x v : A) (l r : BHeap R)
      (eql : ok R v l = true) (eqr : ok R v r = true),
        ok R x (N v l r eql eqr) = R x v)
  (ind :
    forall
      {A : Type} {R : A -> A -> bool}
      (P : BHeap R -> Type)
      (P_E : P E)
      (P_N :
        forall
          (v : A) (l r : BHeap R)
          (eql : ok R v l = true) (eqr : ok R v r = true),
            P l -> P r -> P (N v l r eql eqr)),
      {f : forall h : BHeap R, P h |
        f E = P_E /\
        (forall
          (v : A) (l r : BHeap R)
          (eql : ok R v l = true) (eqr : ok R v r = true),
            f (N v l r eql eqr) = P_N v l r eql eqr (f l) (f r))}).

Definition mirror
  {A : Type} {R : A -> A -> bool} (h : BHeap R) :
  {h' : BHeap R | forall x : A, ok R x h' = ok R x h}.
Proof.
  revert h.
  apply (@ind A R (fun h : BHeap R =>
    {h' : BHeap R | forall x : A, ok R x h' = ok R x h}
  )).
    exists E. reflexivity.
    intros * [l' IHl'] [r' IHr']. eexists (N v r' l' _ _). Unshelve.
      intros. rewrite !ok_N. reflexivity.
      rewrite IHr'. assumption.
      rewrite IHl'. assumption.
Defined.

End BHeap'.
(* end hide *)

(** * Drzewa wyszukiwań binarnych (TODO) *)

(** **** Ćwiczenie *)

(** No cóż, jeszcze raz to samo. Zdefiniuj za pomocą indukcji-rekursji
    jednocześnie typ drzew wyszukiwań binarnych [BST R], gdzie
    [R : A -> A -> bool] rozstrzyga porządek, oraz funkcje
    [oklr]/[okl] i [okr]/[ok], które dbają o odpowiednie warunki (wybierz
    tylko jeden wariant z trzech, które testowałeś w tamtym zadaniu).

    Najpierw napisz pseudodefinicję, a potem przetłumacz ją na odpowiedni
    zestaw aksjomatów.

    Następnie użyj swojej aksjomatycznej definicji, aby zdefiniować funkcję
    [mirror], która tworzy lustrzane odbicie drzewa [t : BST R]. Wskazówka:
    tym razem powinno ci się udać.

    Porównaj induktywno-rekurencyjną implementację [BST R] z implementacją
    przez indukcję-indukcję. Która jest bardziej ogólna? Która jest
    "lżejsza"? Która jest lepsza? *)

(* begin hide *)
Module BST'.

(** TODO: definicja chyba jest źle... *)

(*
Inductive BST {A : Type} (R : A -> A -> bool) : Type :=
| E : BST R
| N : forall (v : A) (l r : BST R),
        okl R v l = true -> okr R v l = true -> BST R

with okl {A : Type} (R : A -> A -> bool) (x : A) (t : BST R) : bool :=
match t with
| E => true
| N v _ _ _ _ => R x v
end

with okr {A : Type} (R : A -> A -> bool) (x : A) (t : BST R) : bool :=
match t with
| E => true
| N v _ _ _ _ => negb (R x v)
*)

Axioms
  (BST : forall {A : Type} (R : A -> A -> bool), Type)
  (okl : forall {A : Type} {R : A -> A -> bool} (x : A) (t : BST R), bool)
  (okr : forall {A : Type} {R : A -> A -> bool} (x : A) (t : BST R), bool)
  (E : forall {A : Type} {R : A -> A -> bool}, BST R)
  (N :
    forall
      {A : Type} {R : A -> A -> bool}
      (v : A)
      (l r : BST R)
      (eql : okl v l = true) (eqr : okr v r = true), BST R)
  (okl_E :
    forall {A : Type} {R : A -> A -> bool} (x : A),
      okl x (@E A R) = true)
  (okl_N :
    forall
      {A : Type} {R : A -> A -> bool}
      (x v : A) (l r : BST R)
      (eql : okl v l = true) (eqr : okr v r = true),
        okl x (N v l r eql eqr) = R x v)
  (okr_E :
    forall {A : Type} {R : A -> A -> bool} (x : A),
      okr x (@E A R) = true)
  (okr_N :
    forall
      {A : Type} {R : A -> A -> bool}
      (x v : A) (l r : BST R)
      (eql : okl v l = true) (eqr : okr v r = true),
        okr x (N v l r eql eqr) = negb (R x v))
  (ind :
    forall
      {A : Type} {R : A -> A -> bool}
      (P : BST R -> Type)
      (P_E : P E)
      (P_N :
        forall
          (v : A) (l r : BST R)
          (eql : okl v l = true) (eqr : okr v r = true),
            P l -> P r -> P (N v l r eql eqr)),
      {f : forall t : BST R, P t |
        f E = P_E /\
        forall
          (v : A) (l r : BST R)
          (eql : okl v l = true) (eqr : okr v r = true),
            f (N v l r eql eqr) = P_N v l r eql eqr (f l) (f r)
      }
  ).

Definition mirror
  {A : Type} {R : A -> A -> bool} (t : BST R) :
    {t' : BST (fun x y : A => negb (R x y)) |
      (forall x : A, okl x t' = okr x t) /\
      (forall x : A, okr x t' = okl x t)}.
Proof.
  revert t.
  apply (@ind A R (fun t : BST R =>
    {t' : BST (fun x y : A => negb (R x y)) |
      (forall x : A, okl x t' = okr x t) /\
      (forall x : A, okr x t' = okl x t)
    }
  )).
    exists E. split; intro; rewrite !okl_E, !okr_E; reflexivity.
    intros v l r eql eqr (l' & IHl1 & IHl2) (r' & IHr1 & IHr2).
      eexists (N v r' l' _ _). Unshelve.
        split; intro; rewrite okl_N, okr_N.
          reflexivity.
          destruct (R x v); reflexivity.
        rewrite IHr1, eqr. reflexivity.
        rewrite IHl2, eql. reflexivity.
Defined.

End BST'.
(* end hide *)

(** * Uniwersa (TODO) *)

(** Podobnie jak poprzednio, pojawia się pytanie: do czego w praktyce
    można użyć indukcji-rekursji (poza rzecz jasna głupimi strukturami
    danych, jak listy posortowane)? W świerszczykach dla bystrzaków
    (czyli tzw. "literaturze naukowej") przewija się głównie jeden (ale
    jakże użyteczny) pomysł: uniwersa.

    Czym są uniwersa i co mają wspólnego z indukcją-rekursją? Najlepiej
    będzie przekonać się na przykładzie programowania generycznego: *)

(** **** Ćwiczenie (zdecydowanie za trudne) *)

(** Zaimplementuj generyczną funkcję [flatten], która spłaszcza dowolnie
    zagnieżdżone listy list do jednej, płaskiej listy.

    [flatten 5 = [5]]

    [flatten [1; 2; 3] = [1; 2; 3]]

    [flatten [[1]; [2]; [3]] = [1; 2; 3]]

    [flatten [[[1; 2]]; [[3]]; [[4; 5]; [6]]] = [1; 2; 3; 4; 5; 6]] *)

(** Trudne, prawda? Ale robialne, a robi się to tak.

    W typach argumentów [flatten] na powyższym przykładzie widać pewien
    wzorzec: są to kolejno [nat], [list nat], [list (list nat)],
    [list (list (list nat))] i tak dalej. Możemy ten "wzorzec" bez problemu
    opisać za pomocą następującego typu: *)

Inductive FlattenType : Type :=
| Nat : FlattenType
| List : FlattenType -> FlattenType.

(** Żeby było śmieszniej, [FlattenType] to dokładnie to samo co [nat], ale
    przemilczmy to. Co dalej? Możemy myśleć o elementach [FlattenType] jak
    o kodach prawdziwych typów, a skoro są to kody, to można też napisać
    funkcję dekodującą: *)

Fixpoint decode (t : FlattenType) : Type :=
match t with
| Nat => nat
| List t' => list (decode t')
end.

(** [decode] każdemu kodowi przyporządkowuje odpowiadający mu typ. O
    kodach możemy myśleć jak o nazwach - [Nat] to nazwa [nat], zaś
    [List t'] to nazwa typu [list (decode t')], np. [List (List Nat)]
    to nazwa typu [list (list nat)].

    Para [(FlattenType, decode)] jest przykładem uniwersum.

    Uniwersum to, najprościej pisząc, worek, który zawiera jakieś typy.
    Formalnie uniwersum składa się z typu kodów (czyli "nazw" typów) oraz
    funkcji dekodującej, która przyporządkowuje kodom prawdziwe typy.

    Programowanie generyczne to programowanie funkcji, które operują na
    kolekcjach typów o dowolnych kształtach, czyli na uniwersach właśnie.
    Generyczność od polimorfizmu różni się tym, że funkcja polimorficzna
    działa dla dowolnego typu, zaś generyczna - tylko dla typu o pasującym
    kształcie.

    Jak dokończyć implementację funkcji [flatten]? Kluczowe jest zauważenie,
    że możemy zdefiniować [flatten] przez rekursję strutkuralną po argumencie
    domyślnym typu [FlattenType]. Ostatni problem to jak zrobić, żeby Coq sam
    zgadywał kod danego typu - dowiemy się tego w rozdziale o klasach.

    Co to wszystko ma wspólnego z uniwersami? Ano, jeżeli chcemy definiować
    bardzo zaawansowane funkcje generyczne, musimy mieć do dyspozycji bardzo
    potężne uniwersa i to właśnie je zapewnia nam indukcja-rekursja. Ponieważ
    w powyższym przykładzie generyczność nie była zbyt wyrafinowana, nie było
    potrzeby używania indukcji-rekursji, jednak uszy do góry: przykład nieco
    bardziej skomplikowanego uniwersum pojawi się jeszcze w tym rozdziale. *)

(** **** Ćwiczenie *)

(** Nieco podchwytliwe zadanie: zdefiniuj uniwersum funkcji [nat -> nat],
    [nat -> (nat -> nat)], [(nat -> nat) -> nat],
    [(nat -> nat) -> (nat -> nat)] i tak dalej, dowolnie zagnieżdżonych.

    Zagadka: czy potrzebna jest nam indukcja-rekursja? *)

(** * Indeksowana indukcja-rekursja i metoda induktywno-rekurencyjnej dziedziny *)

(** Za siedmioma górami, za siedmioma lasami, za siedmioma rzekami, za
    siedmioma budkami telefonicznymi, nawet za indukcją-rekursją (choć
    tylko o kroczek) leży indeksowana indukcja-rekursja, czyli połączenie
    indukcji-rekursji oraz indeksowanych rodzin typów.

    Jako, że w porównaniu do zwykłej indukcji-rekursji nie ma tu za wiele
    innowacyjności, przejdźmy od razu do przykładu przydatnej techniki,
    którą nasza tytułowa bohaterka umożliwia, a jest nią metoda
    induktywno-rekurencyjnej dziedziny - wariant metody induktywnej dziedziny,
    który upraszcza ją w przypadkach, gdy mamy do czynienia z rekursją
    zagnieżdżoną.

    Metoda induktywnej dziedziny polega na tym, żeby zamiast funkcji
    [f : A -> B], która nie jest strukturalnie rekurencyjna (na co Coq
    nie pozwala) napisać funkcję [f : forall x : A, D x -> B], gdzie
    [D : A -> Type] jest "predykatem dziedziny", który sprawia, że dziwna
    rekursja z oryginalnej definicji [f] staje się rekursją strukturalną
    po dowodzie [D x]. Żeby zdefiniować oryginalne [f : A -> B] wystarczy
    udowodnić, że każde [x : A] spełnia predykat dziedziny.

    Co to wszystko ma wspólnego z indeksowaną indukcją-rekursją? Już piszę.
    Otóż metoda ta nie wymaga w ogólności indukcji-rekursji - ta staje się
    potrzebna dopiero, gdy walczymy z bardzo złośliwymi funkcjami, czyli
    takimi, w których rekursja jest zagnieżdżona, tzn. robimy wywołanie
    rekurencyjne na wyniku poprzedniego wywołania rekurencyjnego.

    Predykat dziedziny dla takiej funkcji musi zawierać konstruktor w stylu
    "jeżeli wynik wywołania rekurencyjnego na x należy do dziedziny, to x też
    należy do dziedziny". To właśnie tu ujawnia się indukcja-rekursja: żeby
    zdefiniować predykat dziedziny, musimy odwołać się do funkcji (żeby móc
    powiedzieć coś o wyniku wywołania rekurencyjnego), a żeby zdefiniować
    funkcję, musimy mieć predykat dziedziny.

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


(** * Indukcja-indukcja-rekursja *)

(** Ufff... przebrnęliśmy przez indukcję-indukcję i (indeksowaną)
    indukcję-rekursję. Czy mogą istnieć jeszcze potężniejsze i bardziej
    innowacyjne sposoby definiowania typów przez indukcję?

    Ależ oczywiście. Jest nim... uwaga uwaga, niespodzianka...
    indukcja-indukcja-rekursja, która jest nie tylko strasznym
    potfurem, ale też powinna dostać Oskara za najlepszą nazwę.

    Chodzi tu oczywiście o połączenie indukcji-indukcji i indukcji-rekursji:
    możemy jednocześnie zdefiniować jakiś typ [A], rodzinę typów [B]
    indeksowaną przez [A] oraz operujące na nich funkcje, do których
    konstruktory [A] i [B] mogą się odwoływać.

    Nie ma tu jakiejś wielkiej filozofii: wszystkiego, co powinieneś wiedzieć
    o indukcji-indukcji-rekursji, dowiedziałeś się już z dwóch poprzednich
    podrozdziałów. Nie muszę chyba dodawać, że ława oburzonych jest oburzona
    faktem, że Coq nie wspiera indukcji-indukcji-rekursji.

    Rodzi się jednak to samo super poważne pytanie co zawsze, czyli do czego
    można tego tałatajstwa użyć? Przez całkiem długi czas nie miałem pomysłu,
    ale okazuje się, że jest jedno takie zastosowanie i w sumie narzuca się
    ono samo.

    Przypomnij sobie metodę induktywno-rekurencyjnej dziedziny, czyli jedno
    ze sztandarowych zastosowań indeksowanej indukcji-rekursji. Zaczynamy od
    typu [I : Type], na którym chcemy zdefiniować funkcję o niestandardowym
    kształcie rekursji. W tym celu definiujemy dziedzinę [D : I -> Type]
    wraz z funkcją [f : forall i : I, D i -> R].

    Zauważmy jaki jest związek typu [I] z funkcją [f]: najpierw jest typ,
    potem funkcja. Co jednak, gdy musimy [I] oraz [f] zdefiniować razem za
    pomocą indukcji-rekursji? Wtedy [f] może być zdefiniowane jedynie za
    pomocą rekursji strukturalnej po [I], co wyklucza rekursję o fikuśnym
    kształcie...

    I tu wchodzi indukcja-indukcja-rekursja, cała na biało. Możemy użyć
    jej w taki sposób, że definiujemy jednocześnie:
    - typ [I], który odnosi się do funkcji [f]
    - predykat dziedziny [D : I -> Type], który jest indeksowany przez [I]
    - funkcję [f], która zdefiniowana jest przez rekursję strukturalną po
      dowodzie należenia do dziedziny

    Jak widać, typ zależy od funkcji, funkcja od predykatu, a predykat od
    typu i koło się zamyka.

    Następuje jednak skądinąd uzasadnione pytanie: czy faktycznie istnieje
    jakaś sytuacja, w której powyższy schemat działania jest tym słusznym?
    Odpowiedź póki co może być tylko jedna: nie wiem, ale się domyślam. *)

(** * Promocja 2 w 1 czyli paradoksy Russella i Girarda *)

(** _Istnieje teoria, że jeśli kiedyś ktoś się dowie, dlaczego powstało i
    czemu służy uniwersum, to zniknie ono i zostanie zastąpione czymś
    znacznie dziwaczniejszym i jeszcze bardziej pozbawionym sensu_. *)

(** _Istnieje także teoria, że dawno już tak się stało_. *)

(** Douglas Adams, _Restauracja na końcu wszechświata_ *)

(** W poprzednich podrozdziałach poznaliśmy twierdzenie Cantora oraz
    nauczyliśmy się używać go jako młota na negatywne typy induktywne.

    W tym podrozdziale zapoznamy się z dwoma paradoksami (a precyzyjniej
    pisząc, z dwoma wersjami tego samego paradoksu), które okażą się być
    ściśle powiązane z twierdzeniem Cantora, a które będą służyć nam gdy
    staniemy w szranki z negatwynymi typami induktywno-rekurencyjnymi
    (czyli tymi, które definiuje się przez indukcję-rekursję). O tak: w
    tym podrozdziale, niczym Thanos, staniemy do walki przeciw uniwersum! *)

(** ** Paradoks Russella *)

(** Zacznijmy od paradoksu Russella. Jest to bardzo stary paradoks, odkryty
    w roku 1901 przez... zgadnij kogo... gdy ów człek szukał dziury w całym
    w naiwnej teorii zbiorów (która to teoria, dzięki temu właśnie odkryciu,
    jest już od bardzo dawna dość mocno martwa).

    Sformułowanie paradoksu brzmi następująco: niech V będzie zbiorem
    wszystkich zbiorów, które nie należą same do siebie. Pytanie: czy
    V należy do V?

    Gdzie tu paradoks? Otóż jeżeli V należy do V, to na mocy definicji V,
    V nie należy do V. Jeżeli zaś V nie należy do V, to na mocy definicji V,
    V należy do V. Nie trzeba chyba dodawać, że jednoczesne należenie i
    nienależenie prowadzi do sprzeczności.

    Na czym tak naprawdę polega paradoks? Jakiś mądry (czyli przemądrzały)
    filozof mógłby rzec, że na nadużyciu pojęcia zbioru... albo czymś
    równie absurdalnym. Otóż nie! Paradoks Russella polega na tym samym,
    co cała masa innych paradoksów, czyli na autoreferencji.

    Z autoreferencją spotkaliśmy się już co najmniej raz, w rozdziale
    pierwszym. Przypomnij sobie, że golibroda goli tych i tylko tych,
    którzy sami siebie nie golą. Czy golibroda goli sam siebie? Takie
    postawienie sprawy daje paradoks. Podobnie z Russellem: V zawiera
    te i tylko te zbiory, które nie zawierają same siebie. Czy V zawiera
    V? Wot, paradoks. Żeby lepiej wczuć się w ten klimat, czas na więcej
    ćwiczeń. *)

(** **** Ćwiczenie *)

(** To genialne ćwiczenie wymyśliłem dzięki zabłądzeniu na esperanckiej
    Wikipedii (ha! nikt nie spodziewał się esperanckiej Wikipedii w
    ćwiczeniu dotyczącym paradoksu Russella). Ćwiczenie brzmi tak:

    W Wikipedii niektóre artykuły są listami (nie, nie w sensie typu
    induktywnego :)), np. lista krajów według PKB per capita. Pytanie:
    czy można stworzyć w Wikipedii listę wszystkich list? Czy na liście
    wszystkich list ona sama jest wymieniona? Czy można w Wikipedii
    stworzyć listę wszystkich list, które nie wymieniają same siebie? *)

(** ** Paradoks Girarda *)

From Typonomikon Require Import D2z.

(** Dobra, wystarczy już tych paradoksów... a nie, czekaj. Przecież został
    nam do omówienia jeszcze paradoks Girarda. Jednak poznawszy już tajniki
    autoreferencji, powinno pójść jak z płatka.

    Paradoks Girarda to paradoks, który może zaistnieć w wielu systemach
    formalnych, takich jak teorie typów, języki programowania, logiki i
    inne takie. Źródłem całego zła jest zazwyczaj stwierdzenie w stylu
    [Type : Type]. *)

Check Type.
(* ===> Type : Type *)

(** O nie! Czyżbyśmy właśnie zostali zaatakowani przez paradoks Girarda?
    W tym miejscu należy przypomnieć (albo obwieścić - niestety nie pamiętam,
    czy już o tym wspominałem), że [Type] jest w Coqu jedynie synonimem dla
    czegoś w stylu [Type(i)], gdzie [i] jest "poziomem" sortu [Type], zaś
    każde [Type(i)] żyje tak naprawdę w jakimś [Type(j)], gdzie [j] jest
    większe od [i] - typy niższego poziomu żyją w typach wyższego poziomu.
    Będziesz mógł ów fakt ujrzeć na własne oczy, gdy w CoqIDE zaznaczysz
    opcję [View > Display universe levels]. *)

Check Type.
(* ===> Type@{Top.590} : Type@{Top.590+1} *)

(** Jak widać, jest mniej więcej tak jak napisałem wyżej. Nie przejmuj się
    tym tajemniczym [Top] - to tylko nic nieznaczący bibelocik. W twoim
    przypadku również poziom uniwersum może być inny niż [590]. Co więcej,
    poziom ten będzie się zwiększał wraz z każdym odpaleniem komendy [Check
    Type] (czyżbyś pomyślał właśnie o doliczeniu w ten sposób do zyliona?).

    Skoro już wiemy, że NIE zostaliśmy zaatakowani przez paradoks Girarda,
    to w czym problem z tym całym [Type : Type]? Jakiś przemądrzały (czyli
    mądry) adept informatyki teoretycznej mógłby odpowiedzieć, że to zależy
    od konkretnego systemu formalnego albo coś w tym stylu. Otóż niet! Jak
    zawsze, chodzi oczywiście o autoreferencję.

    Gdyby ktoś był zainteresowany, to najlepsze dotychczas sformułowanie
    paradoksu znalazłem (zupełnie przez przypadek, wcale nie szukając) w
    pracy "An intuitionistic theory of types" Martina-Löfa (swoją drogą,
    ten koleś wymyślił podstawy dużej części wszystkiego, czym się tutaj
    zajmujemy). Można ją przeczytać tu (paradoks Girarda jest pod koniec
    pierwszej sekcji):
    archive-pml.github.io/martin-lof/pdfs/An-Intuitionistic-Theory-of-Types-1972.pdf

    Nasze sformułowanie paradoksu będzie podobne do tego z powyższej pracy
    (co jest w sumie ciekawe, bo wymyśliłem je samodzielnie i to przez
    przypadek), ale dowód sprzeczności będzie inny - na szczęście dużo
    prostszy (albo i nie...).

    Dobra, koniec tego ględzenia. Czas na konkrety. *)

(*
Fail Inductive U : Type :=
| Pi : forall (A : U) (B : El A -> U), U
| UU : U

with El (u : U) : Type :=
match u with
| Pi A B => forall x : El A, B x
| UU => U
end.
*)

(** Powyższa induktywno-rekurencyjna definicja typu [U] (i interpretującej
    go funkcji [El]), którą Coq rzecz jasna odrzuca (uczcijmy ławę oburzonych
    minutą oburzenia) to definicja pewnego uniwersum.

    W tym miejscu wypadałoby wytłumaczyć, czym są uniwersa. Otóż odpowiedź
    jest dość prosta: uniwersum składa się z typu [U : Type] oraz funkcji
    [El : U -> Type]. Intuicja w tym wszystkim jest taka, że elementami
    typu [U] są nazwy typów (czyli bytów sortu [Type]), zaś fukncja [El]
    zwraca typ, którego nazwę dostanie.

    Choć z definicji widać to na pierwszy rzut oka, to zaskakujący może
    wydać ci się fakt, że w zasadzie każdy typ można zinterpretować jako
    uniwersum i to zazwyczaj na bardzo wiele różnych sposobów (tyle ile
    różnych interpretacji [El] jesteśmy w stanie wymyślić). Najlepiej
    będzie, jeżeli przemyślisz to wszystko w ramach ćwiczenia. *)

(** **** Ćwiczenie *)

(** Ćwiczenie będzie konceptualne, a składa się na nie kilka łamigłówek:
    - zinterpretuj [False] jako uniwersum
    - zinterpretuj [unit] jako uniwersum (ile jest możliwych sposobów?)
    - czy istnieje uniwersum, które zawiera nazwę samego siebie? Uwaga:
      to nie jest tak proste, jak może się wydawać na pierwszy rzut oka.
    - wymyśl ideologicznie słuszną interpretację typu [nat] jako uniwersum
      (tak, jest taka). Następnie wymyśl jakąś głupią interpretację [nat]
      jako uniwersum. Dlaczego ta interpretacja jest głupia?
    - zdefiniuj uniwersum, którego elementami są nazwy typów funkcji z
      n-krotek liczb naturalnych w liczby naturalne. Uwaga: rozwiązanie
      jest bardzo eleganckie i możesz się go nie spodziewać.
    - czy istnieje uniwersum, którego interpretacja jest surjekcją? Czy
      da się w Coqu udowodnić, że tak jest albo nie jest? Uwaga: tak
      bardzo podchwytliwe, że aż sam się złapałem. *)

(* begin hide *)

(** Odpowiedzi:
    - [False] to uniwersum puste, w którym nic nie ma - a myślałeś, że co?
    - [unit] to uniwersum zawierające nazwę jednego, wybranego typu - też
      niezbyt odkrywcza odpowiedź. Interpretacji jest tyle ile typów.
    - Tak, istnieje uniwersum zawierające nazwę samego siebie, np. [unit].
    - Ideologicznie słuszna interpretacja [nat] to uniwersum typów
      skończonych - [El n] to typ n-elementowy. Głupia interpretacja:
      każde [n] jest nazwą dla tego samego typu, np. [nat].
    - Tutaj mały twist, bo tym uniwersum też jest [nat]
    - Tutaj też trochę twist, bo takie uniwersum oczywiście istnieje i
      nazywa się... baram bam bam bam... fanfary... [Type]! No cóż, nie
      tego się spodziewałeś, prawda? A co do tego, czy istnieje takie
      induktywne uniwersum, to myślę, że dla każdego kandydata z osobna
      dałoby się pokazać, że nie jest ono wystarczająco dobre. *)

(* end hide *)

(** Skoro wiemy już, czym są uniwersa, przyjrzyjmy się temu, które właśnie
    zdefiniowaliśmy. Żebyś nie musiał w rozpaczy przewijać do góry, tak
    wygląda aksjomatyczne kodowanie tego uniwersum: *)

Module PoorUniverse.

Axioms
  (U : Type)
  (El : U -> Type)

  (Pi : forall (A : U) (B : El A -> U), U)
  (UU : U)

  (El_Pi :
    forall (A : U) (B : El A -> U),
      El (Pi A B) = forall (x : El A), El (B x))
  (El_UU : El UU = U)

  (ind : forall
    (P : U -> Type)
    (PPi :
      forall (A : U) (B : El A -> U),
        P A -> (forall x : El A, P (B x)) -> P (Pi A B))
    (PUU : P UU),
      {f : forall u : U, P u |
        (forall (A : U) (B : El A -> U),
          f (Pi A B) =
          PPi A B (f A) (fun x : El A => f (B x))) /\
        (f UU = PUU)
      }
  ).

(** [U] to typ, którego elementami są nazwy typów, zaś [El] jest jego
    interpretacją. Nazwy możemy tworzyć tylko na dwa sposoby: jeżeli [A : U]
    jest nazwą typu, zaś [B : El A -> U] jest rodziną nazw typów indeksowaną
    przez elementy typu [A], to [Pi A B] jest nazwą typu
    [forall x : El A, El (B x)]. Drugim konstruktorem jest [UU], które
    oznacza nazwę samego uniwersum, tzn. [El UU = U].

    Reguła indukcji jest dość prosta: jeżeli [P : U -> Type] jest rodziną
    typów (tych prawdziwych) indeksowaną przez [U] (czyli nazwy typów), to
    żeby zdefiniować funkcję [f : forall u : U, P u] musimy mieć dwie rzeczy:
    po pierwsze, musimy pokazać, że [P (Pi A B)] zachodzi, gdy zachodzi [P A]
    oraz [P (B x)] dla każdego [x : El A]. Po drugie, musi zachodzić [P UU].

    Mimo, że uniwersum wydaje się biedne, jest ono śmiertelnie sprzeczne,
    gdyż zawiera nazwę samego siebie. Jeżeli rozwiązałeś (poprawnie, a nie
    na odwal!) ostatnie ćwiczenie, to powinieneś wiedzieć, że niektóre
    uniwersa mogą zawierać nazwy samego siebie i wcale to a wcale nie daje
    to żadnych problemów.

    Dlaczego więc w tym przypadku jest inaczej? Skoro [UU] nie jest złe samo
    w sobie, to problem musi leżeć w [Pi], bo niby gdzie indziej? Zobaczmy
    więc, gdzie kryje się sprzeczność. W tym celu posłużymy się twierdzeniem
    Cantora: najpierw zdefiniujemy surjekcję [U -> (U -> U)], a potem pokażemy,
    za pomocą metody przekątniowej, że taka surjekcja nie może istnieć. *)

(*
Definition extract (u : U) : U -> U :=
match u with
| Pi UU B => B
| _ => fun u : U => U
end.
*)

(** Jeżeli dostajemy [Pi A B], gdzie [A] to [UU], to wtedy [B : El A -> U]
    tak naprawdę jest typu [U -> U] (bo [El UU = U]). W innych przypadkach
    wystarczy po prostu zwrócić funkcję identycznościową. Niestety Coq nie
    wspiera indukcji-rekursji (ława oburzonych), więc funkcję [extract] musimy
    zdefiniować ręcznie: *)

Definition extract : U -> (U -> U).
Proof.
  apply (ind (fun _ => U -> U)).
    intros A B _ _. revert A B.
      apply (ind (fun A : U => (El A -> U) -> (U -> U))).
        intros; assumption.
        intro B. rewrite El_UU in B. exact B.
    exact (fun u : U => u).
Defined.

(** Powyższa definicja za pomocą taktyk działa dokładnie tak samo jak
    nieformalna definicja [extract] za pomocą dopasowania do wzorca. Jedyna
    różnica jest taka, że [El UU] nie jest definicyjnie równe [U], lecz
    są one jedynie zdaniowo równe na mocy aksjomatu [El_UU : El UU = U].
    Musimy więc przepisać go w [B], żeby typy się zgadzały.

    Zanim będziemy mogli pokazać, że [extract] jest surjekcją, czeka nas kilka
    niemiłych detali technicznych (gdyby [El UU] i [U] były definicyjnie
    równe, wszystkie te problemy by zniknęły). *)

Check eq_rect.
(* ===> forall (A : Type) (x : A) (P : A -> Type),
          P x -> forall y : A, x = y -> P y *)

Check eq_rect_r.
(* ===> forall (A : Type) (x : A) (P : A -> Type),
          P x -> forall y : A, y = x -> P y *)

(** [eq_rect] oraz [eq_rect_r] to groźnie wyglądające lematy, ale sprawa tak
    na prawdę jest dość prosta: to one wykonują całą pracę za każdym razem,
    kiedy używasz taktyki [rewrite]. Jeżeli cel jest postaci [P x] i użyjemy
    na nim [rewrite H], gdzie [H : x = y], to [rewrite] zamienia cel na
    [eq_rect _ _ _ cel _ H], które jest już typu [P y]. [eq_rect_r] działa
    podobnie, ale tym razem równość jest postaci [y = x] (czyli obrócona).

    Ponieważ w definicji [extract] używaliśmy [rewrite]'a, to przy dowodzeniu,
    że [extract] jest surjekcją, będziemy musieli zmierzyć się właśnie z
    [eq_rect] i [eq_rect_r]. Stąd poniższy lemat, który mówi mniej więcej,
    że jeżeli przepiszemy z prawa na lewo, a potem z lewa na prawo, to tak,
    jakby nic się nie stało. *)

Lemma right_to_left_to_right :
  forall
    (A : Type) (P : A -> Type) (x y : A) (p : x = y) (u : P y),
      eq_rect x P (@eq_rect_r A y P u x p) y p = u.
Proof.
  destruct p. cbn. reflexivity.
Qed.

(** Dowód jest banalny. Ponieważ [eq_rect] i [eq_rect_r] są zdefiniowane
    przez dopasowanie do wzorca [p : x = y], to wystarczy [p] potraktować
    [destruct]em, a dalej wszystko już ładnie się oblicza. *)

Lemma surjective_extract :
  surjective extract.
Proof.
  unfold surjective, extract.
  intro f.
  destruct (ind _) as [extract [extract_Pi extract_UU]].
  destruct (ind _) as [extract' [extract'_Pi extract'_UU]].
  pose (f' := eq_rect_r (fun T : Type => T -> U) f El_UU).
  exists (Pi UU f').
  unfold f'.
  rewrite extract_Pi, extract'_UU, right_to_left_to_right.
  reflexivity.
Qed.

(** Dlaczego [extract] jest surjekcją? Intuicyjnie pisząc, każdą funkcję
    [U -> U] możemy włożyć do konstruktora [Pi] jako jego drugi argument,
    jeżeli tylko zamienimy pierwsze [U] na [El UU]. Skoro każdą możemy
    tam włożyć, to każdą możemy wyjąć. Ot i cały sekret.

    Technicznie dowód realizujemy tak: odwijamy definicje i wprowadzamy do
    kontekstu funkcję [f]. Następnie rozbijamy [ind _] pochodzące z definicji
    [extract], rozkładając w ten sposób definicję [extract] na właściwe
    [extract] (sama funkcja), [extract'] (wewnętrzna funkcja pomocnicza) oraz
    równania dla [extract] i [extract'] dla poszczególnych przypadków.

    Następnie musimy znaleźć takie [a : U], że [extract a = f]. Robimy to, co
    zasugerowałem wyżej, czyli w [f : U -> U] pierwsze [U] zamieniamy na
    [El UU], uzyskując w ten sposób [f']. Temu właśnie służy użycie
    [eq_rect_r] (nie używamy [rewrite], bo potrzeba nam większej precyzji).

    Wobec tego szukanym przez nas elementem [U], któremu [extract] przyporządkuje
    [f], jest [Pi UU f']. Możemy w tym miejscu odwinąć definicję [f']. Gdyby
    Coq wspierał indukcję-rekursję, to w tym miejscu wystarczyłoby użyć tylko
    [reflexivity] - [extract (Pi UU f')] obliczyłoby się do [f] na mocy definicji
    [extract] oraz dzięki temu, że [El UU] obliczyłoby się do [U]. Niestety Coq
    nie wspiera indukcji rekursji (ława oburzonych), więc musimy wszystkie
    te trzy kroki obliczeń wykonać ręcznie za pomocą taktyki [rewrite].

    Ufff, udało się! Jeżeli przeraża cię ten dowód - nie martw się. Chodzi
    w nim o to samo, o co chodziło w poprzednich dowodach bycia surjekcją.
    Ten jest po prostu trochę bardziej skomplikowany, bo indukcja-rekursja
    jest nieco bardziej skomplikowana do użycia w Coqu niż prymitywniejsze
    formy indukcji. *)

Definition modify : U -> U.
Proof.
  apply ind.
    intros. exact UU.
    exact (Pi UU (fun _ => UU)).
Defined.

(** Teraz czas udowodnić, że [extract] nie jest surjekcją. Zrobimy to metodą
    przekątniową, a w tym celu potrzebować będziemy funkcji [U -> U], która
    dla każdego argumentu zwraca coś, co jest od niego różne.

    Na szczęście sprawa jest prosta: jeżeli argumentem jest [Pi A B], to
    zwracamy [UU], zaś jeżeli [UU], to zwracamy [Pi UU (fun _ => UU)]. *)

Definition discern : U -> bool.
Proof.
  apply ind.
    intros. exact true.
    exact false.
Defined.

(** Przydałaby się też funkcja, która pozwoli nam rozróżnić konstruktory
    typu [U]. Normalnie użylibyśmy do tego taktyki [inversion], ale
    używamy kodowania aksjomatycznego, więc [inversion] nie zadziała i
    musimy ręcznie zaimplementować sobie coś w jej stylu.

    Nasza funkcja dla [Pi] zwraca [true], a dla [UU] daje [false]. *)

Lemma modify_neq :
  forall u : U, modify u <> u.
Proof.
  apply ind.
    intros A B H1 H2 eq.
      apply (f_equal discern) in eq.
      unfold modify, discern in eq.
      destruct (ind _) as [d [d_Pi d_UU]],
               (ind _) as [ch [ch_Pi ch_UU]].
      rewrite d_Pi, ch_Pi, d_UU in eq. inversion eq.
    intro eq.
      apply (f_equal discern) in eq.
      unfold modify, discern in eq.
      destruct (ind _) as [d [d_Pi d_UU]],
               (ind _) as [ch [ch_Pi ch_UU]].
      rewrite ch_UU, d_Pi, d_UU in eq. inversion eq.
Qed.

(** Wypadałoby też pokazać, ża nasza funkcja działa tak, jak sobie tego
    życzymy. Dowód jest bardzo prosty, ale aksjomatyczne kodowanie znacznie
    go zaciemnia.

    Zaczynamy od indukcji po [u : U]. W pierwszym przypadku mamy hipotezę
    [eq : modify (Pi A B) = Pi A B], a skoro tak, to po zaaplikowaniu
    [discern] musi być także [discern (modify (Pi A B)) = discern (Pi A B)].

    Następnie rozkładamy definicje [modify] i [discern] na atomy ([modify]
    nazywa się teraz [ch], a [discern] nazywa się [d]). Przepisujemy
    odpowiednie równania w hipotezie [eq], dzięki czemu uzyskujemy
    [false = true], co jest sprzeczne. Drugi przypadek jest analogiczny. *)

Lemma extract_not_sur :
  ~ surjective extract.
Proof.
  unfold surjective. intro.
  destruct (H (fun u : U => modify (extract u u))) as [u eq].
  apply (f_equal (fun f => f u)) in eq.
  apply (modify_neq (extract u u)). symmetry. assumption.
Qed.

(** Teraz możemy już pokazać, że [extract] nie jest surjekcją. W tym celu
    wyobraźmy sobie [extract] jako kwadratową tabelkę, której wiersze i
    kolumny są indeksowane przez [U]. Tworzymy nową funkcję [U -> U]
    biorąc elementy z przekątnej i modyfikując je za pomocą [modify].

    Skoro [extract] jest surjekcją, to ta nowa funkcja musi być postaci
    [extract u] dla jakiegoś [u : U]. Aplikując obie strony jeszcze raz
    do [u] dostajemy równanie [extract u u = modify (extract u u)], które
    jest sprzeczne na mocy lematu [modify_neq]. *)

Definition U_illegal : False.
Proof.
  apply extract_not_sur. apply surjective_extract.
Qed.

(** Ponieważ [extract] jednocześnie jest i nie jest surjekcją, nastepuje nagły
    atak sprzeczności. Definicja uniwersum [U] przez indukcję-rekursję jest
    nielegalna. Tak właśnie prezentuje się paradoks Girarda w Coqowym wydaniu. *)

End PoorUniverse.

(** **** Ćwiczenie *)

(** Tak naprawdę, to w tym podrozdziale byliśmy co najwyżej bieda-Thanosem,
    gdyż uniwersum, z którym się ścieraliśmy, samo było biedne. W niniejszym
    ćwiczeniu zmierzysz się z uniwersum, które zawiera też nazwy typu pustego,
    typu [unit] i liczb naturalnych, nazwy produktów, sum i funkcji, a także
    sum zależnych.

    Mówiąc wprost: zakoduj aksjomatycznie poniższą definicję uniwersum [U],
    a następnie udowodnij, że jest ona nielegalna. Nie powinno to być
    trudne - metoda jest podobna jak w przypadku biednego uniwersum. *)

Module NonPoorUniverse.

(*
Fail Inductive U : Type :=
| Empty : U
| Unit : U
| Nat : U
| Prod : U -> U -> U
| Sum : U -> U -> U
| Arr : U -> U -> U
| Pi : forall (A : U) (B : El A -> U), U
| Sigma: forall (A : U) (B : El A -> U), U
| UU : U

with El (u : U) : Type :=
match u with
| Empty => Empty_set
| Unit => unit
| Nat => nat
| Prod A B => El A * El B
| Sum A B => El A + El B
| Arr A B => El A -> El B
| Pi A B => forall x : El A, B x
| Sigma A B => {x : El A & El (B x)}
| UU => U
end.
*)

(* begin hide *)
Axioms
  (U : Type)
  (El : U -> Type)

  (Empty : U)
  (Unit : U)
  (Nat : U)
  (Prod : U -> U -> U)
  (Sum : U -> U -> U)
  (Arr : U -> U -> U)
  (Pi : forall (A : U) (B : El A -> U), U)
  (Sigma : forall (A : U) (B : El A -> U), U)
  (UU : U)

  (El_Empty : El Empty = Empty_set)
  (El_Unit : El Unit = unit)
  (El_Nat : El Nat = nat)
  (El_Prod : forall A B : U, El (Prod A B) = (El A * El B)%type)
  (El_Sum : forall A B : U, El (Sum A B) = (El A + El B)%type)
  (El_Arr : forall A B : U, El (Arr A B) = El A -> El B)
  (El_Pi :
    forall (A : U) (B : El A -> U),
      El (Pi A B) = forall (x : El A), El (B x))
  (El_Sigma :
    forall (A : U) (B : El A -> U),
      El (Pi A B) = {x : El A & El (B x)})
  (El_UU : El UU = U)

  (ind : forall
    (P : U -> Type)
    (PEmpty : P Empty)
    (PUnit : P Unit)
    (PNat : P Nat)
    (PProd :
      forall A B : U, P A -> P B -> P (Prod A B))
    (PSum :
      forall A B : U, P A -> P B -> P (Sum A B))
    (PArr :
      forall A B : U, P A -> P B -> P (Arr A B))
    (PPi :
      forall (A : U) (B : El A -> U),
        P A -> (forall x : El A, P (B x)) -> P (Pi A B))
    (PSigma :
      forall (A : U) (B : El A -> U),
        P A -> (forall x : El A, P (B x)) -> P (Sigma A B))
    (PUU : P UU),
      {f : forall A : U, P A |
        (f Empty = PEmpty) /\
        (f Unit = PUnit) /\
        (f Nat = PNat) /\
        (forall A B : U,
          f (Prod A B) = PProd A B (f A) (f B)) /\
        (forall A B : U,
          f (Sum A B) = PSum A B (f A) (f B)) /\
        (forall A B : U,
          f (Arr A B) = PArr A B (f A) (f B)) /\
        (forall (A : U) (B : El A -> U),
          f (Pi A B) =
          PPi A B (f A) (fun x : El A => f (B x))) /\
        (forall (A : U) (B : El A -> U),
          f (Sigma A B) =
          PSigma A B (f A) (fun x : El A => f (B x))) /\
        (f UU = PUU)
      }).

Definition extract : U -> (U -> U).
Proof.
  apply (ind (fun _ => U -> U)).
    1-6,8-9: intros; assumption.
    intros A B _ _. revert A B.
      apply (ind (fun A : U => (El A -> U) -> (U -> U))).
        1-8: intros; assumption.
        intro f. rewrite El_UU in f. exact f.
Defined.

Lemma right_to_left_to_right :
  forall
    (A : Type) (P : A -> Type) (x y : A) (p : x = y) (u : P y),
      eq_rect x P (@eq_rect_r A y P u x p) y p = u.
Proof.
  destruct p. cbn. reflexivity.
Qed.

Lemma surjective_extract :
  surjective extract.
Proof.
  unfold surjective, extract; intro f.
  destruct (ind _) as [g H]; decompose [and] H; clear H.
  destruct (ind _) as [h H']; decompose [and] H'; clear H'.
  pose (f' := eq_rect_r (fun T : Type => T -> U) f El_UU).
  exists (Pi UU f').
  rewrite H6. rewrite H17.
  unfold f'. rewrite right_to_left_to_right. reflexivity.
Qed.

Definition modify : U -> U.
Proof.
  apply ind.
    exact Nat.
    all: intros; exact Empty.
Defined.

Definition discern : U -> nat.
Proof.
  apply ind; intros.
    exact 0.
    exact 1.
    exact 2.
    exact 3.
    exact 4.
    exact 5.
    exact 6.
    exact 7.
    exact 8.
Defined.

Ltac help H :=
  apply (f_equal discern) in H;
  cbn in H; unfold discern in H;
  destruct (ind _) as [help Hhelp];
  decompose [and] Hhelp; clear Hhelp;
  congruence.

Lemma modify_neq :
  forall u : U, modify u <> u.
Proof.
  apply ind; unfold modify;
  destruct (ind _) as [f H]; decompose [and] H; clear H;
  intros; try help H; help H9.
Qed.

Lemma extract_not_sur :
  ~ surjective extract.
Proof.
  unfold surjective. intro.
  destruct (H (fun u : U => modify (extract u u))) as [u eq].
  apply (f_equal (fun f => f u)) in eq.
  apply (modify_neq (extract u u)). symmetry. assumption.
Qed.
(* end hide *)

Lemma U_illegal : False.
(* begin hide *)
Proof.
  apply extract_not_sur. apply surjective_extract.
Qed.
(* end hide *)

End NonPoorUniverse.