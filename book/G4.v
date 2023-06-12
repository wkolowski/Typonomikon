(** * G4: Indukcja-indukcja *)

Require Import List.
Import ListNotations.

(** * Wstęp (TODO) *)

Module ind_ind.

(** Po powtórce nadszedł czas nowości. Zacznijmy od nazwy, która jest iście
    kretyńska: indukcja-indukcja. Każdy rozsądny człowiek zgodzi się,
    że dużo lepszą nazwą byłoby coś w stylu "indukcja wzajemna indeksowana".

    Ta alternatywna nazwa rzuca sporo światła: indukcja-indukcja to połączenie
    i uogólnienie mechanizmów definiowania typów wzajemnie induktywnych oraz
    indeksowanych typów induktywnych.

    Typy wzajemnie induktywne mogą odnosić się do siebie nawzajem, ale co
    to dokładnie znaczy? Ano to, że konstruktory każdego typu mogą brać
    argumenty wszystkch innych typów definiowanych jednocześnie z nim. To
    jest clou całej sprawy: konstruktory.

    A co to ma do typów indeksowanych? Ano, zastanówmy się, co by się stało,
    gdybyśmy chcieli zdefiniować przez wzajemną indukcję typ [A] oraz rodzinę
    typów [B : A -> Type]. Otóż nie da się: konstruktory [A] mogą odnosić
    się do [B] i vice-versa, ale [A] nie może być indeksem [B].

    Indukcja-indukcja to coś, co... tam taram tam tam... pozwala właśnie na
    to: możemy jednocześnie zdefiniować typ i indeksowaną nim rodzinę typów.
    I wszystko to ukryte pod taką smutną nazwą... lobby teoriotypowe nie
    chciało, żebyś się o tym dowiedział.

    Czas na przykład! *)

(** * Listy posortowane *)

Fail

Inductive slist {A : Type} (R : A -> A -> Prop) : Type :=
| snil : slist R
| scons : forall (h : A) (t : slist A), ok h t -> slist A

with ok {A : Type} {R : A -> A -> Prop} : A -> slist R -> Prop :=
| ok_snil : forall x : A, ok x snil
| ok_scons :
    forall (h : A) (t : slist A) (p : ok h t) (x : A),
      R x h -> ok x (scons h t p).

(* ===> The reference slist was not found in the current environment. *)

(** Jako się już wcześniej rzekło, indukcja-indukcja nie jest wspierana
    przez Coqa - powyższa definicja kończy się informacją o błędzie: Coq
    nie widzi [slist] kiedy czyta indeksy [ok] właśnie dlatego, że nie
    dopuszcza on możliwości jednoczesnego definiowania rodziny (w tym
    wypadku relacji) [ok] wraz z jednym z jej indeksów, [slist].

    Będziemy zatem musieli poradzić sobie z przykładem jakoś inaczej -
    po prostu damy go sobie za pomocą aksjomatów. Zanim jednak to zrobimy,
    omówimy go dokładniej, gdyż deklarowanie aksjomatów jest niebezpieczne
    i nie chcemy się pomylić.

    Zamysłem powyższego przykładu było zdefiniowanie typu list posortowanych
    [slist R], gdzie [R] pełni rolę relacji porządku, jednocześnie z relacją
    [ok : A -> slist R -> Prop], gdzie [ok x l] wyraża, że dostawienie [x]
    na początek listy posortowanej [l] daje listę posortowaną.

    Przykład jest oczywiście dość bezsensowny, bo dokładnie to samo można
    osiągnąć bez używania indukcji-indukcji - wystarczy najpierw zdefiniować
    listy, a potem relację bycia listą posortowaną, a na koniec zapakować
    wszystko razem. Nie będziemy się tym jednak przejmować.

    Definicja [slist R] jest następująca:
    - [snil] to lista pusta
    - [scons] robi posortowaną listę z głowy [h] i ogona [t] pod warunkiem, że
      dostanie też dowód zdania [ok h t] mówiącego, że można dostawić [h] na
      początek listy [t] *)

(** Definicja [ok] też jest banalna:
    - każdy [x : A] może być dostawiony do pustej listy
    - jeżeli mamy listę [scons h t p] oraz element [x], o którym wiemy,
      że jest mniejszy od [h], tzn. [R x h], to [x] może zostać dostawiony
      do listy [scons h t p] *)

(** Jak powinny wyglądać reguły rekursji oraz indukcji? Na szczęście wciąż
    działają schematy, które wypracowaliśmy dotychczas.

    Reguła rekursji mówi, że jeżeli znajdziemy w typie [P] coś o kształcie
    [slist R], a w relacji [Q] coś o kształcie [ok], to możemy zdefiniować
    funkcję [slist R -> P] oraz [forall (x : A) (l : slist R), ok x l -> Q].

    Regułe indukcji można uzyskać dodając tyle zależności, ile tylko zdołamy
    unieść.

    Zobaczmy więc, jak zrealizować to wszystko za pomocą aksjomatów. *)

Axioms
  (slist : forall {A : Type}, (A -> A -> Prop) -> Type)
  (ok : forall {A : Type} {R : A -> A -> Prop}, A -> slist R -> Prop).

(** Najpierw musimy zadeklarować [slist], gdyż wymaga tego typ [ok]. Obie
    definicje wyglądają dokładnie tak, jak nagłówki w powyższej definicji
    odrzuconej przez Coqa.

    Widać też, że gdybyśmy chcieli zdefiniować rodziny [A] i [B], które są
    nawzajem swoimi indeksami, to nie moglibyśmy tego zrobić nawet za pomocą
    aksjomatów. Rodzi to pytanie o to, które dokładnie definicje przez
    indukcję-indukcję są legalne. Odpowiedź brzmi: nie wiem, ale może kiedyś
    się dowiem. *)

Axioms
  (snil : forall {A : Type} {R : A -> A -> Prop}, slist R)
  (scons :
    forall {A : Type} {R : A -> A -> Prop} (h : A) (t : slist R),
      ok h t -> slist R)
  (ok_snil :
    forall {A : Type} {R : A -> A -> Prop} (x : A), ok x (@snil _ R))
  (ok_scons :
    forall
      {A : Type} {R : A -> A -> Prop}
      (h : A) (t : slist R) (p : ok h t)
      (x : A), R x h -> ok x (scons h t p)).

(** Następnie definiujemy konstruktory: najpierw konstruktory [slist], a
    potem [ok]. Musimy to zrobić w tej kolejności, bo konstruktor [ok_snil]
    odnosi się do [snil], a [ok_scons] do [scons].

    Znowu widzimy, że gdyby konstruktory obu typów odnosiły się do siebie
    nawzajem, to nie moglibyśmy zdefiniować takiego typu aksjomatycznie. *)

Axiom
  (ind : forall
    (A : Type) (R : A -> A -> Prop)
    (P : slist R -> Type)
    (Q : forall (h : A) (t : slist R), ok h t -> Type)
    (Psnil : P snil)
    (Pscons :
      forall (h : A) (t : slist R) (p : ok h t),
        P t -> Q h t p -> P (scons h t p))
    (Qok_snil : forall x : A, Q x snil (ok_snil x))
    (Qok_scons :
      forall
        (h : A) (t : slist R) (p : ok h t)
        (x : A) (H : R x h),
          P t -> Q h t p -> Q x (scons h t p) (ok_scons h t p x H)),
    {f : (forall l : slist R, P l) &
    {g : (forall (h : A) (t : slist R) (p : ok h t), Q h t p) |
      f snil = Psnil /\
      (forall (h : A) (t : slist R) (p : ok h t),
        f (scons h t p) = Pscons h t p (f t) (g h t p)) /\
      (forall x : A,
        g x snil (ok_snil x) = Qok_snil x) /\
      (forall
        (h : A) (t : slist R) (p : ok h t)
        (x : A) (H : R x h),
          g x (scons h t p) (ok_scons h t p x H) =
          Qok_scons h t p x H (f t) (g h t p))
    }}).

(** Ugh, co za potfur. Spróbujmy rozłożyć go na czynniki pierwsze.

    Przede wszystkim, żeby za dużo nie pisać, zobaczymy tylko regułę indukcji.
    Teoretycznie powinny to być dwie reguły (tak jak w przypadku [Smok]a i
    [Zmok]a) - jedna dla [slist] i jedna dla [ok], ale żeby za dużo nie
    pisać, możemy zapisać je razem.

    Typ [A] i relacja [R] są parametrami obu definicji, więc skwantyfikowane
    są na samym początku. Nasza reguła pozwala nam zdefiniować przez wzajemną
    rekursję dwie funkcje, [f : forall l : slist R, P l] oraz
    [g : forall (h : A) (t : slist R) (p : ok h t), Q h t p]. Tak więc [P]
    to kodziedzina [f], a [Q] - [g].

    Teraz potrzebujemy rozważyć wszystkie możliwe przypadki - tak jak przy
    dopasowaniu do wzorca. Przypadek [snil] jest dość banalny. Przypadek
    [scons] jest trochę cięższy. Przede wszystkim chcemy, żeby konkluzja
    była postaci [P (scons h t p)], ale jak powinny wyglądać hipotezy
    indukcyjne?

    Jedyna słuszna odpowiedź brzmi: odpowiadają one typom wszystkich możliwych
    wywołań rekurencyjnych [f] i [g] na strukturalnych podtermach
    [scons h t p]. Jedynymi typami spełniającymi te warunki są [P t] oraz
    [Q h t p], więc dajemy je sobie jako hipotezy indukcyjne.

    Przypadki dla [Q] wyglądają podobnie: [ok_snil] jest banalne, a dla
    [ok_scons] konkluzja musi być jedynej słusznej postaci, a hipotezami
    indukcyjnymi jest wszystko, co pasuje.

    W efekcie otrzymujemy dwie funkcje, [f] i [g]. Tym razem następuje jednak
    mały twist: ponieważ nasza definicja jest aksjomatyczna, zagwarantować
    musimy sobie także reguły obliczania, które dotychczas były zamilaczne,
    bo wynikały z definicji przez dopasowanie do wzorca. Teraz wszystkie te
    "dopasowania" musimy napisać ręcznie w postaci odpowiednio
    skwantyfikowanych równań. Widzimy więc, że [Psnil], [Pscons], [Qok_snil]
    i [Qok_scons] odpowiadają klauzulom w dopasowaniu do wzorca.

    Ufff... udało się. Tak spreparowaną definicją aksjomatyczną możemy się
    jako-tako posługiwać: *)

Definition rec'
  {A : Type} {R : A -> A -> Prop}
  (P : Type) (snil' : P) (scons' : A -> P -> P) :
  {f : slist R -> P |
    f snil = snil' /\
    forall (h : A) (t : slist R) (p : ok h t),
      f (scons h t p) = scons' h (f t)
  }.
Proof.
  destruct
  (
    ind
    A R
    (fun _ => P) (fun _ _ _ => True)
    snil' (fun h _ _ t _ => scons' h t)
    (fun _ => I) (fun _ _ _ _ _ _ _ => I)
  )
  as (f & g & H1 & H2 & H3 & H4).
  exists f. split.
    exact H1.
    exact H2.
Defined.

(** Możemy na przykład dość łatwo zdefiniować niezależny rekursor tylko dla
    [slist], nie odnoszący się w żaden sposób do [ok]. Widzimy jednak, że
    "programowanie" w taki aksjomatyczny sposób jest dość ciężkie - zamiast
    eleganckich dopasowań do wzorca musimy ręcznie wpisywać argumenty do
    reguły indukcyjnej. *)

Definition toList'
  {A : Type} {R : A -> A -> Prop} :
  {f : slist R -> list A |
    f snil = [] /\
    forall (h : A) (t : slist R) (p : ok h t),
      f (scons h t p) = h :: f t
  }.
Proof.
  exact (rec' (list A) [] cons).
Defined.

Definition toList
  {A : Type} {R : A -> A -> Prop} : slist R -> list A :=
    proj1_sig toList'.

(** Używanie takiego rekursora jest już dużo prostsze, co ilustruje powyższy
    przykład funkcji, która zapomina o tym, że lista jest posortowana i daje
    nam zwykłą listę.

    Przykładowe posortowane listy wyglądają tak: *)

Definition slist_01 : slist le :=
  scons 0
    (scons 1
      snil
      (ok_snil 1))
    (ok_scons 1 snil (ok_snil 1) 0 (le_S 0 0 (le_n 0))).

(** Niezbyt piękna, prawda? *)

(* Compute toList slist_01. *)

(** Utrapieniem jest też to, że nasza funkcja się nie oblicza. Jest tak, bo
    została zdefiniowana za pomocą reguły indukcji, która jest aksjomatem.
    Aksjomaty zaś, jak wiadomo, nie obliczają się.

    Wyniku powyższego wywołania nie będę nawet wklejał, gdyż jest naprawdę
    ohydny. *)

Lemma toList_slist_01_result :
  toList slist_01 = [0; 1].
Proof.
  unfold toList, slist_01.
  destruct toList' as (f & H1 & H2); cbn.
  rewrite 2!H2, H1. reflexivity.
Qed.

(** Najlepsze, co możemy osiągnąć, mając taką definicję, to udowodnienie, że
    jej wynik faktycznie jest taki, jak się spodziewamy. *)

(** **** Ćwiczenie *)

(** Zdefiniuj dla list posortowanych funkcję [slen], która liczy ich długość.
    Udowodnij oczywiste twierdzenie wiążące ze sobą [slen], [toList] oraz
    [length]. *)

(* begin hide *)

Definition slen'
  {A : Type} {R : A -> A -> Prop} :
  {f : slist R -> nat |
    f snil = 0 /\
    forall (h : A) (t : slist R) (p : ok h t),
      f (scons h t p) = S (f t)}.
Proof.
  exact (rec' nat 0 (fun _ n => S n)).
Defined.

Definition slen {A : Type} {R : A -> A -> Prop} : slist R -> nat :=
  proj1_sig slen'.

Lemma slen_toList_length :
  forall {A : Type} {R : A -> A -> Prop} (l : slist R),
    slen l = length (toList l).
Proof.
  intros A R.
  eapply (projT1 (
    ind A R (fun l => slen l = length (toList l))
      (fun _ _ _ => True)
      _ _
      (fun _ => I)
      (fun _ _ _ _ _ _ _ => I))).
  Unshelve.
  all: cbn; unfold slen, toList;
  destruct slen' as (f & Hf1 & Hf2), toList' as (g & Hg1 & Hg2); cbn.
    rewrite Hf1, Hg1. cbn. reflexivity.
    intros. rewrite Hf2, Hg2, H. cbn. reflexivity.
Qed.

(* end hide *)

(** ** Przykład był bez sensu... (TODO) *)

(** **** Ćwiczenie *)

(** Udowodnij, że przykład faktycznie jest bez sensu: zdefiniuje relację
    [sorted : (A -> A -> Prop) -> list A -> Prop], gdzie [sorted R l]
    oznacza, że lista [l] jest posortowana według porządku [R]. Używając
    [sorted] zdefiniuj typ list posortowanych [slist' R], a następnie znajdź
    dwie funkcje [f : slist R -> slist' R] i [f : slist' R -> slist R],
    które są swoimi odwrotnościami. *)

(* begin hide *)

Inductive sorted {A : Type} (R : A -> A -> Prop) : list A -> Prop :=
| sorted_nil : sorted R []
| sorted_singl : forall x : A, sorted R [x]
| sorted_cons :
    forall (x y : A) (t : list A),
      R x y -> sorted R (y :: t) -> sorted R (x :: y :: t).

Arguments sorted_nil   {A R}.
Arguments sorted_singl {A R} _.
Arguments sorted_cons  {A R x y t} _ _.

Definition slist' {A : Type} (R : A -> A -> Prop) : Type :=
  {l : list A | sorted R l}.

Lemma toList_sorted :
  forall {A : Type} {R : A -> A -> Prop} (l : slist R),
    sorted R (toList l).
Proof.
  intros A R.
  refine (projT1 (ind
    A R
    (fun l => sorted R (toList l))
    (fun x t _ =>
      t = snil \/
      exists (h : A) (t' : slist R) (p : ok h t'),
        t = scons h t' p /\ R x h)
    _ _ _ _)).
  1-2: unfold toList; destruct toList' as (f & H1 & H2); cbn.
    rewrite H1. constructor.
    intros. rewrite H2. decompose [or ex and] H0; clear H0; subst.
      rewrite H1. constructor.
      rewrite H2 in *. constructor; assumption.
    intros. left. reflexivity.
    intros. decompose [or ex and] H1; clear H1; subst.
      right. exists h, snil, p. split; trivial.
      right. exists h, (scons x0 x1 x2), p. split; trivial.
Qed.

(** TODO *)

(* end hide *)

(** **** Ćwiczenie *)

(** Żeby przekonać się, że przykład był naprawdę bezsensowny, zdefiniuj
    rodzinę typów [blist : (A -> A -> Prop) -> A -> Type], gdzie elementami
    [blist R x] są listy posortowane, których elementy są [R]-większe od [x].
    Użyj [blist] do zdefiniowania typu [slist'' R], a następnie udowodnij,
    że [slist R] i [slist'' R] są sobie równoważne. *)

(* begin hide *)
(* TODO: rozwiąż ćwiczenie *)
(* end hide *)

End ind_ind.

(** * Teoria typów w teorii typów za pomocą indukcji-indukcji *)

(** Na koniec wypadałoby jeszcze wspomnieć, do czego tak naprawdę można w
    praktyce użyć indukcji-indukcji (definiowanie list posortowanych nie
    jest jedną z tych rzeczy, o czym przekonałeś się w ćwiczeniach). Otóż
    najciekawszym przykładem wydaje się być formalizacja teorii typów, czyli,
    parafrazując, implementacja Coqa w Coqu.

    Żeby się za to zabrać, musimy zdefiniować konteksty, typy i termy, a
    także relacje konwertowalności dla typów i termów. Są tutaj możliwe dwa
    podejścia:
    - Curry'ego (ang. Curry style lub mądrzej extrinsic style) - staramy
      się definiować wszystko osobno, a potem zdefiniować relacje "term x
      jest typu A w kontekście Γ", "typ A jest poprawnie sformowany w
      kontekście Γ" etc. Najważniejszą cechą tego sposobu jest to, że
      możemy tworzyć termy, którym nie da się przypisać żadnego typu oraz
      typy, które nie są poprawnie sformowane w żadnym kontekście.
    - Churcha (ang. Church style lub mądrzej intrinsic style) - definiujemy
      wszystko na raz w jednej wielkiej wzajemnej indukcji. Zamiastów
      typów definiujemy od razu predykat "typ A jest poprawnie sformowany
      w kontekście Γ", a zamiast termów definiujemy od razu relację
      "term x ma typ A w kontekście Γ". Parafrazując - wszystkie termy,
      które jesteśmy w stanie skonstruować, są poprawnie typowane (a
      wszystkie typy poprawnie sformowane w swoich kontekstach). *)

(** Zamiast tyle gadać zobaczmy, jak mogłoby to wyglądać w Coqu. Oczywiście
    będą to same nagłówki, bo podanie tutaj pełnej definicji byłoby mocno
    zaciemniającym przegięciem. *)

(*
Inductive Ctx : Type := ...

with Ty : Ctx -> Type := ...

with Term : forall Γ : Ctx, Ty Γ -> Type := ...

with TyConv : forall Γ : Ctx, Ty Γ -> Ty Γ -> Prop := ...

with
  TermConv :
    forall (Γ : Ctx) (A : Ty Γ),
      Term Γ A -> Term Γ A -> Prop := ...
*)

(** Nagłówki w tej definicji powinniśmy interpretować tak:
    - [Ctx] to typ reprezentujący konteksty.
    - [Ty] ma reprezentować typy, ale nie jest to typ, lecz rodzina typów
      indeksowana kontekstami - każdy typ jest typem w jakimś kontekście,
      np. [list A] jest typem w kontekście zawierającym [A : Type], ale
      nie jest typem w pustym kontekście.
    - [Term] ma reprezentować termy, ale nie jest to typ, lecz rodzina typów
      indeksowana kontekstami i typami - każdy term ma jakiś typ, a typy,
      jak już się rzekło, zawsze są typami w jakimś kontekście. Przykład:
      jeżeli [x] jest zmienną, to [cons x nil] jest typu [list A] w
      kontekście, w którym [x] jest typu [A], ale nie ma żadnego typu (i nie
      jest nawet poprawnym termem) w kontekście pustym ani w żadnym, w którym
      nie występuje [x].
    - [TyConv Γ A B] zachodzi, gdy typy [A] i [B] są konwertowalne, czyli
      obliczają się do tego samego (relacja taka jest potrzebna, gdyż w Coqu
      i ogólnie w teorii typów występować mogą takie typy jak [if true then
      nat else bool], który jest konwertowalny z [nat]). Jako się rzekło,
      typy zawsze występują w kontekście, więc konwertowalne mogą być też
      tylko w kontekście.
    - [TermConv Γ A x y] znaczy, że termy [x] i [y] są konwertowalne,
      np. [if true then 42 else 0] jest konwertowalne z [42]. Ponieważ każdy
      term ciągnie za sobą swój typ, [TermConv] ma jako indeks typ [A], a
      ponieważ typ ciągnie za sobą kontekst, indeksem [TermConv] jest także
      [Γ]. *)

(** Jak widać, indukcji-indukcji jest w powyższym przykładzie na pęczki -
    jest ona wręcz teleskopowa, gdyż [Ctx] jest indeksem [Ty], [Ctx] i [Ty]
    są indeksami [Term], a [Ctx], [Ty] i [Term] są indeksami [TermConv].

    Cóż, to by było na tyle w tym temacie.
    #<a class='link' href='https://www.sadistic.pl/lawa-oburzonych-vt22270.htm'>
    Ława oburzonych</a># wyraża w tym momencie swoje najwyższe oburzenie na brak
    indukcji-indukcji w Coqu.

    Jednak uszy do góry - istnieją już języki, które jakoś sobie radzą z
    indukcją-indukcją. Jednym z nich jest wspomniana we wstępie
    #<a class='link' href='https://agda.readthedocs.io/en/latest/'>Agda</a>#. *)

(** * Sterty binarne *)

(** **** Ćwiczenie *)

(** Typ stert binarnych [BHeap R], gdzie [R : A -> A -> Prop] jest relacją
    porządku, składa się z drzew, które mogą być albo puste, albo być węzłem
    przechowującym wartość [v : A] wraz z dwoma poddrzewami [l r : BHeap R],
    przy czym [v] musi być [R]-większe od wszystkich elementów [l] oraz [r].

    Użyj indukcji-indukcji, żeby zdefiniować jednocześnie typ [BHeap R] oraz
    relację [ok], gdzie [ok v h] zachodzi, gdy [v] jest [R]-większe od
    wszystkich elementów [h].

    Najpierw napisz pseudodefinicję, a potem przetłumacz ją na odpowiedni
    zestaw aksjomatów.

    Następnie użyj swojej aksjomatycznej definicji, aby zdefiniować funkcję
    [mirror], która tworzy lustrzane odbicie sterty [h : BHeap R]. Wskazówka:
    prawdopodobnie nie uda ci się zdefiniować [mirror]. Zastanów się,
    dlaczego jest tak trudno. *)

(* begin hide *)

Module BHeap.

Fail

Inductive BHeap {A : Type} (R : A -> A -> Prop) : Type :=
| E : BHeap R
| N : forall (v : A) (l r : BHeap R), ok v l -> ok v r -> BHeap R

with ok {A : Type} {R : A -> A -> Prop} : A -> BHeap R -> Prop :=
| ok_E : forall v : A, ok v E
| ok_N :
    forall (v x : A) (l r : BHeap A) (pl : ok x l) (pr : ok x r),
      R x v -> ok v (N x l r pl pr).

Axioms
  (BHeap : forall {A : Type} (R : A -> A -> Prop), Type)
  (ok : forall {A : Type} {R : A -> A -> Prop}, A -> BHeap R -> Prop)
  (E : forall {A : Type} {R : A -> A -> Prop}, BHeap R)
  (N :
    forall
      {A : Type} {R : A -> A -> Prop}
      (v : A) (l r : BHeap R),
        ok v l -> ok v r -> BHeap R)
  (ok_E : forall {A : Type} {R : A -> A -> Prop} (v : A), ok v (@E _ R))
  (ok_N :
    forall
      {A : Type} {R : A -> A -> Prop}
      (v x : A) (l r : BHeap R) (pl : ok x l) (pr : ok x r),
        R x v -> ok v (N x l r pl pr))
  (ind : forall
    (A : Type) (R : A -> A -> Prop)
    (P : BHeap R -> Type)
    (Q : forall (v : A) (h : BHeap R), ok v h -> Type)
    (PE : P E)
    (PN : forall (v : A) (l r : BHeap R) (pl : ok v l) (pr : ok v r),
            P l -> P r -> Q v l pl -> Q v r pr -> P (N v l r pl pr))
    (Qok_E :
      forall v : A, Q v E (ok_E v))
    (Qok_N :
      forall
        (v x : A) (l r : BHeap R) (pl : ok x l) (pr : ok x r) (H : R x v),
          P l -> P r -> Q x l pl -> Q x r pr ->
            Q v (N x l r pl pr) (ok_N v x l r pl pr H)),
    {f : forall h : BHeap R, P h &
    {g : forall (v : A) (h : BHeap R) (p : ok v h), Q v h p |
      f E = PE /\
      (forall (v : A) (l r : BHeap R) (pl : ok v l) (pr : ok v r),
        f (N v l r pl pr) =
        PN v l r pl pr (f l) (f r) (g v l pl) (g v r pr)) /\
      (forall v : A, g v E (ok_E v) = Qok_E v) /\
      (forall
        (v x : A) (l r : BHeap R) (pl : ok x l) (pr : ok x r) (H : R x v),
          g v (N x l r pl pr) (ok_N v x l r pl pr H) =
          Qok_N v x l r pl pr H (f l) (f r) (g x l pl) (g x r pr))
    }}).

(*
Definition mirror
  {A : Type} {R : A -> A -> Prop}
  :
  {f : BHeap R -> BHeap R &
  {g : forall {v : A} {h : BHeap R}, ok v h -> ok v (f h) |
    f E = E /\
    (forall (v : A) (l r : BHeap R) (pl : ok v l) (pr : ok v r),
      f (N v l r pl pr) = N v (f r) (f l) (g v r pr) (g v l pl)) /\
    (forall v : A, g v E (ok_E v) = ok_E v)
  }}.
Proof.
  Check (
    ind
      A R
      (fun _ => BHeap R)). 
      (fun _ _ _ => True)
      E (fun v _ _ _ _ l' r' pl' pr' => N v r' l' pr' pl')
      (fun _ => I) (fun _ _ _ _ _ _ _ _ _ _ _ => I)
  ).
*)

End BHeap.

(* end hide *)

(** * Drzewa wyszukiwań binarnych (TODO) *)

(** **** Ćwiczenie *)

(** Typ drzew wyszukiwań binarnych [BST R], gdzie [R : A -> A -> Prop] jest
    relacją porządku, składa się z drzew, które mogą być albo puste, albo być
    węzłem przechowującym wartość [v : A] wraz z dwoma poddrzewami
    [l r : BST R], przy czym [v] musi być [R]-większe od wszystkich elemtnów
    [l] oraz [R]-mniejsze od wszystkich elementów [r].

    Użyj indukcji-indukcji, żeby zdefiniować jednocześnie typ [BST R] wraz
    z odpowiednimi relacjami zapewniającymi poprawność konstrukcji węzła.
    Wypróbuj trzy podejścia:
    - jest jedna relacja, [oklr], gdzie [oklr v l r] oznacza, że z [v], [l] i
      [r] można zrobić węzeł
    - są dwie relacje, [okl] i [okr], gdzie [okl v l] oznacza, że [v] jest
      [R]-większe od wszystkich elementów [l], zaś [okr v r], że [v] jest
      [R]-mniejsze od wszystkich elementów [r]
    - jest jedna relacja, [ok], gdzie [ok v t] oznacza, że [v] jest
      [R]-mniejsze od wszystkich elementów [t] *)

(** Najpierw napisz pseudodefinicję, a potem przetłumacz ją na odpowiedni
    zestaw aksjomatów.

    Następnie użyj swojej aksjomatycznej definicji, aby zdefiniować funkcję
    [mirror], która tworzy lustrzane odbicie drzewa [t : BST R]. Wskazówka:
    dość możliwe, że ci się nie uda. *)

(* begin hide *)

(** TODO: przetłumacz na odpowiedni zestaw aksjomatów, zdefiniuj mirror *)

Module BST.

Fail

Inductive BST {A : Type} (R : A -> A -> Prop) : Type :=
| E : BST R
| N : forall (v : A) (l r : BST R), ok v l r -> BST R

with ok {A : Type} {R : A -> A -> Prop} : A -> BST R -> BST R -> Prop :=
| ok_EE : forall v : A, ok v E E
| ok_EN :
    forall (v vl : A) (ll lr : BST R),
      R vl v -> ok v (N vl ll lr) E
| ok_NE :
    forall (v vr : A) (rl rr : BST R),
      R v vr -> ok v E (N vr rl rr)
| ok_NN :
    forall (v vl vr : A) (ll lr rl rr : BST R),
      R vl v -> R v vr -> ok v (N vl ll lr) (N vr rl rr).

Fail

Inductive BST {A : Type} (R : A -> A -> Prop) : Type :=
| E : BST R
| N : forall (v : A) (l r : BST R), okl v l -> okr v r -> BST R

with okl {A : Type} {R : A -> A -> Prop} : A -> BST R -> Prop :=
| okl_E : forall v : A, okl v E
| okl_N :
    forall (v vl : A) (ll lr : BST R),
      R vl v -> okl v (N vl ll lr)

with okr {A : Type} {R : A -> A -> Prop} : A -> BST R -> Prop :=
| okr_E : forall v : V, okr v E
| okr_N :
    forall (v vr : A) (rl rr : BST R),
      R v vr -> okr v (N vr rl rr).

Definition inv {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
  fun x y => R y x.

Fail

Inductive BST {A : Type} (R : A -> A -> Prop) : Type :=
| E : BST R
| N : forall (v : A) (l r : BST R),
        @ok A R v l -> @ok A (inv R) v r -> BST R

with ok {A : Type} {R : A -> A -> Prop} : A -> BST R -> Prop :=
| ok_E : forall v : A, ok v E
| ok_N : forall (v x : A) (l r : BST R),
           R x v -> ok v (N x l r).

End BST.

(* end hide *)