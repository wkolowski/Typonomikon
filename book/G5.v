(** * G5: Indukcja-rekursja *)

Require Import List.
Import ListNotations.

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

(** * Indeksowana indukcja-rekursja *)

(** Za siedmioma górami, za siedmioma lasami, za siedmioma rzekami, za
    siedmioma budkami telefonicznymi, nawet za indukcją-rekursją (choć
    tylko o kroczek) leży indeksowana indukcja-rekursja, czyli połączenie
    indukcji-rekursji oraz indeksowanych rodzin typów.

    Jako, że w porównaniu do zwykłej indukcji-rekursji nie ma tu za wiele
    innowacyjności, przejdźmy od razu do przykładu przydatnej techniki,
    którą nasza tytułowa bohaterka umożliwia, a zwie się on metodą
    induktywnej dziedziny.

    Pod tą nazwą kryje się sposób definiowania funkcji, pozwalający oddzielić
    samą definicję od dowodu jej terminacji. Jeżeli ten opis nic ci nie mówi,
    nie martw się: dotychczas definiowaliśmy tylko tak prymitywne funkcje, że
    tego typu fikołki nie były nam potrzebne.

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
    należy do dziedziny".To właśnie tu ujawnia się indukcja-rekursja: żeby
    zdefiniować predykat dziedziny, musimy odwołać się do funkcji (żeby móc
    powiedzieć coś o wyniku wywołania rekurencyjnego), a żeby zdefiniować
    funkcję, musimy mieć predykat dziedziny.

    Brzmi skomplikowanie? Jeżeli czegoś nie rozumiesz, to jesteś debi...
    a nie, czekaj. Jeżeli czegoś nie rozumiesz, to nie martw się: powyższy
    przykład miał na celu jedynie zilustrować jakieś praktyczne zastosowanie
    indeksowanej indukcji-rekursji. Do metody induktywnej dziedziny powrócimy
    w kolejnym rozdziale. Pokażemy, jak wyeliminować z niej indukcję-rekursję,
    tak żeby uzyskane za jej pomocą definicje można było odpalać w Coqu.
    Zobaczymy też, jakimi sposobami dowodzić, że każdy element dziedziny
    spełnia predykat dziedziny, co pozwoli nam odzyskać oryginalną definicję
    funkcji, a także dowiemy się, jak z "predykatu" o typie [D : A -> Type]
    zrobić prawdziwy predykat [D : A -> Prop]. *)

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