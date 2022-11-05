(** * G1: Uniwersa kodów i programowanie generyczne [TODO] *)

(** Tutaj o programowaniu generycznym za pomocą uniwersów kodów. Na końcu
    generycznie zajmiemy się typami (ko)induktywnymi, badając W- i M-typy,
    a potem oparte na nich uniwersa kodów.

    Być może to właśnie tutaj jest odpowiednie miejsce aby wprowadzić
    indukcję-rekursję. *)

(** * Uniwersa kodów a programowanie generyczne *)

(** ** Spłaszczanie wielokrotnie zagnieżdżonych list *)

Require Import List.
Import ListNotations.

Module Flatten.

Inductive Star : Type :=
| Var : Type -> Star
| List : Star -> Star.

Fixpoint interp (s : Star) : Type :=
match s with
| Var A => A
| List s' => list (interp s')
end.

Fixpoint flattenType (s : Star) : Type :=
match s with
| Var A => A
| List s' => flattenType s'
end.

Fixpoint flatten {s : Star} : interp s -> list (flattenType s) :=
match s with
| Var A => fun x : interp (Var A) => [x]
| List s' =>
  fix f (x : list (interp s')) : list (flattenType s') :=
  match x with
  | [] => []
  | h :: t => @flatten s' h ++ f t
  end
end.

Compute @flatten (List (List (Var nat))) [[1; 2; 3]; [4; 5; 6]].
Compute
  @flatten
    (List (List (List (Var nat))))
    [[[1]; [2; 2]; [3]]; [[4; 5; 6]]].

Class HasStar (A : Type) : Type :=
{
    star : Star;
    no_kidding : interp star = A;
}.

#[refine]
#[export]
Instance HasStar_any (A : Type) : HasStar A | 1 :=
{
    star := Var A;
}.
Proof.
  cbn. reflexivity.
Defined.

#[refine]
#[export]
Instance HasStar_list (A : Type) (hs : HasStar A) : HasStar (list A) | 0 :=
{
    star := List star;
}.
Proof.
  cbn. rewrite no_kidding. reflexivity.
Defined.

Definition flatten'
  {A : Type} {_ : HasStar A} (x : A) : list (flattenType star).
Proof.
  apply flatten. rewrite no_kidding. exact x. Show Proof.
Defined.

Compute flatten' [[1; 2; 3]; [4; 5; 6]].
Compute flatten' [[[1]; [2; 2]; [3]]; [[4; 5; 6]]].

End Flatten.

(** ** [zipWith] z dowolną ilością argumentów *)

From Typonomikon Require D5.

Module ZipWithN.

Import D5.

Inductive Code : Type :=
| Singl : Type -> Code
| Cons : Type -> Code -> Code.

Fixpoint cmap (F : Type -> Type) (c : Code) : Code :=
match c with
| Singl A => Singl (F A)
| Cons A c' => Cons (F A) (cmap F c')
end.

Fixpoint funType (c : Code) (R : Type) : Type :=
match c with
| Singl A => A -> R
| Cons A c' => A -> funType c' R
end.

Definition listType (c : Code) (R : Type) : Type :=
  funType (cmap list c) R.

Fixpoint prod (c : Code) : Type :=
match c with
| Singl A => A
| Cons A c' => A * prod c'
end.

Definition prodList (c : Code) : Type :=
  prod (cmap list c).

Definition listProd (c : Code) : Type :=
  list (prod c).

Definition uncurriedFunType (c : Code) (R : Type) : Type :=
  prod c -> R.

Definition uncurriedListType (c : Code) (R : Type) : Type :=
  prodList c -> R.

Fixpoint zip2 {A B : Type} (l : list A) (r : list B) : list (A * B) :=
match l, r with
| [], _ => []
| _, [] => []
| hl :: tl, hr :: tr => (hl, hr) :: zip2 tl tr
end.

Fixpoint zip {c : Code} : prodList c -> listProd c :=
match c with
| Singl A => id
| Cons A c' =>
  fun '(l, p) => zip2 l (zip p)
end.

Compute
  @zip
    (Cons bool (Singl nat))
    ([true; false], [4; 5]).

Fixpoint uncurryFun
  {c : Code} {R : Type} {struct c} : funType c R -> uncurriedFunType c R.
Proof.
  destruct c; cbn in *; intro f; red; cbn.
    exact f.
    intros [t p]. exact (uncurryFun _ _ (f t) p).
Defined.

Fixpoint curryList
  {c : Code} {R : Type} {struct c} : uncurriedListType c R -> listType c R.
Proof.
  destruct c as [A | A c']; unfold uncurriedListType; cbn in *.
    intros f l. exact (f l).
    intros f l. apply curryList. red. intro. apply f. split; assumption.
Defined.

Definition zipWith
  {c : Code} {R : Type} (f : funType c R) : listType c (list R) :=
    curryList (fun p : prodList c => map (uncurryFun f) (zip p)).

Compute
  @zipWith
    (Cons nat (Cons nat (Singl nat))) _
    (fun a b c => a + b + c)
    [1; 2; 3] [4; 5; 6] [7; 8; 9].

End ZipWithN.

(** ** Porządna negacja (albo i nie) [TODO] *)

(** Pomysł: silną negację można zdefiniować przez rekursję po uniwersum
    kodów, w którym są kody na wszystkie potrzebne typy. *)

From Typonomikon Require D1 D2.

Module Negation.

(*
Inductive U : Type :=
| F : U
| T : U
| And : U -> U -> U
| Or : U -> U -> U
| Impl : U -> U -> U.
*)

Import D1 D2.
Import PoorUniverse.

End Negation.

(** * W-typy (TODO) *)

Inductive W (A : Type) (B : A -> Type) : Type :=
| sup : forall x : A, (B x -> W A B) -> W A B.

Arguments sup {A B} _ _.

(* begin hide *)

(** Agenda (różnice między W i typami induktywnymi):
    - W potrzebują funext do indukcji
    - typy induktywne są w Coqu generatywne, a W-typy nie są. Jaśniej:
      jeżeli mamy moduł parametryczny, to każda instancjacja parametru
      skutkuje stworzeniem nowego typu induktywnego, mimo że mają one
      takie same nazwy etc. W-typy są bliższe idei uniwersum nazw na
      typy induktywne (ale nie do końca)
    - jeżeli uniwersum ma regułę eliminacji, to [W] umożliwia programowanie
      generyczne *)

(* end hide *)

(** W-typy (ang. W-types) to typy dobrze ufundowanych drzew (ang.
    well-founded trees - W to skrót od well-founded), tzn. skończonych drzew
    o niemal dowolnych kształtach wyznaczanych przez parametry [A] i [B].

    Nie są one zbyt przydatne w praktyce, gdyż wszystko, co można za ich
    pomocą osiągnąć, można też osiągnąć bez nich zwykłymi typami induktywnymi
    i będzie to dużo bardziej czytelne oraz prostsze w implementacji. Ba!
    W-typy są nawet nieco słabsze, gdyż go udowodnienia reguły indukcji
    wymagają aksjomatu ekstensjonalności dla funkcji.

    Jednak z tego samego powodu są bardzo ciekawe pod względem teoretycznym -
    wszystko, co można zrobić za pomocą parametryzowanych typów induktywnych,
    można też zrobić za pomocą samych W-typów. Dzięki temu możemy badanie
    parametryzowanych typów induktywnych, których jest mniej więcej
    nieskończoność i jeszcze trochę, sprowadzić do badania jednego tylko [W]
    (o ile godzimy się na aksjomat ekstensjonalności dla funkcji).

    Zanim jednak zobaczymy przykłady ich wykorzystania, zastanówmy się przez
    kilka chwil, dlaczego są one tak ogólne.

    Sprawa jest dość prosta. Rozważmy typ induktywny [T] i dowolny z jego
    konstruktorów [c : X1 -> ... -> Xn -> T]. Argumenty [Xi] możemy podzielić
    na dwie grupy: argumenty nieindukcyjne (oznaczmy je literą [A]) oraz
    indukcyjne (które są postaci [T]). Wobec tego typ [c] możemy zapisać jako
    [c : A1 -> ... -> Ak -> T -> ... -> T -> T].

    W kolejnym kroku łączymy argumenty za pomocą produktu:
    niech [A := A1 * ... * Ak]. Wtedy typ [c] wygląda tak:
    [c : A -> T * ... * T -> T]. Zauważmy, że [T * ... * T] możemy zapisać
    równoważnie jako [B -> T], gdzie [B] to typ mający tyle elementów, ile
    razy [T] występuje w produkcie [T * ... * T]. Zatem typ [c] przedstawia
    się tak: [c : A -> (B -> T) -> T].

    Teraz poczynimy kilka uogólnień. Po pierwsze, na początku założyliśmy,
    że [c] ma skończenie wiele argumentów indukcyjnych, ale postać [B -> T]
    uwzględnia także przypadek, gdy jest ich nieskończenie wiele (tzn. gdy
    [c] miał oryginalnie jakiś argument postaci [Y -> T] dla nieskończonego
    [Y]).

    Po drugie, założyliśmy, że [c] jest funkcją niezależną. Przypadek, gdy
    [c] jest funkcją zależną możemy pokryć, pozwalając naszemu [B] zależeć
    od [A], tzn. [B : A -> Type]. Typ konstruktora [c] zyskuje wtedy postać
    sumy zależnej [{x : A & B x -> T} -> T]. W ostatnim kroku odpakowujemy
    sumę i [c] zyskuje postać [c : forall x : A, B x -> T].

    Jak więc widać, typ każdego konstruktora można przekształcić tak, żeby
    móc zapisać go jako [forall x : A, B x -> T]. Zauważmy też, że jeżeli
    mamy dwa konstruktory [c1 : forall x : A1, B1 x -> T] oraz
    [c2 : forall x : A2, B2 x -> T], to możemy równie dobrze zapisać je
    za pomocą jednego konstruktora [c]: niech [A := A1 + A2] i niech
    [B (inl a1) := B1 a1, B (inl a2) := B2 a2]. Wtedy konstruktory [c1] i
    [c2] są równoważne konstruktorowi [c].

    Stosując powyższe przekształcenia możemy sprowadzić każdy typ induktywny
    do równoważnej postaci z jednym konstruktorem o typie
    [forall x : A, B x -> T]. Skoro tak, to definiujemy nowy typ, w którym
    [A] i [B] są parametrami... i bum, tak właśnie powstało [W]!

    Podejrzewam, że powyższy opis przyprawia cię o niemały ból głowy. Rzućmy
    więc okiem na przykład, który powinien być wystarczająco ogólny, żeby
    wszystko stało się jasne. *)

Print list.
(* ===> Inductive list (X : Type) : Type :=
        | nil : list X
        | cons : X -> list X -> list X *)

(** Spróbujmy zastosować powyższe przekształcenia na typie [list X], żeby
    otrzymać reprezentację [list] za pomocą [W].

    Zajmijmy się najpierw konstruktorem [nil]. Nie ma on ani argumentów
    indukcyjnych, ani nieindukcyjnych, co zdaje się nie pasować do naszej
    ogólnej metody. Jest to jednak jedynie złudzenie: brak argumentów
    nieindukcyjnych możemy zareprezentować za pomocą argumenu o typie
    [unit], zaś brak argumentów indukcyjnych możemy zareprezentować
    argumentem o typie [False -> list X]. Wobec tego typ konstruktora
    [nil] możemy zapisać jako [unit -> (False -> list X) -> list X].

    Dla [cons]a jest już prościej: argument nieindukcyjny to po prostu [X],
    zaś jeden argument indukcyjny możemy przedstawić jako [unit -> list X].
    Nowy typ [cons]a możemy zapisać jako [X -> (unit -> list X) -> list X].

    Pozostaje nam skleić obydwa konstruktory w jeden. Niech [A := unit + X]
    i niech [B (inl tt) := False, B (inr x) := unit]. W ten sposób dostajemy
    poniższe kodowanie [list] za pomocą [W] (oczywiście nie jest to jedyne
    możliwe kodowanie - równie dobrze zamiast [unit + X] moglibyśmy użyć
    typu [option X]). *)

Require Import FunctionalExtensionality.

Module listW.

Definition listW (X : Type) : Type :=
  W (unit + X) (
    fun ux : unit + X =>
    match ux with
    | inl _ => False
    | inr _ => unit
    end).

(** Wartą zauważenia różnicą konceptualną jest to, że jeżeli myślimy
    Coqowymi typami induktywnymi, to [list] ma dwa konstruktory - [nil]
    i [cons], ale gdy myślimy za pomocą [W], to sprawa ma się inaczej.
    Formalnie [listW] ma jeden konstruktor [sup], ale w praktyce jest
    aż [1 + |X|] konstruktorów, gdzie [|X|] oznacza liczbę elementów
    typu [X]. Jeden z nich opdowiada [nil], a każdy z pozostałych [|X|]
    konstruktorów odpowiada [cons x] dla pewnego [x : X]. Jedyną
    pozostałością po oryginalnej liczbie konstruktorów jest liczba
    składników, które pojawiają się w sumie [unit + X].

    Oczywiście posługiwanie się [nil] i [cons] jest dużo wygodniejsze niż
    używanie [sup], więc czas odzyskać utracone konstruktory! *)

Definition nilW (X : Type) : listW X :=
  sup (inl tt) (fun e : False => match e with end).

Definition consW {X : Type} (h : X) (t : listW X) : listW X :=
  sup (inr h) (fun _ : unit => t).

(** Zauważ, że [consW] jest jedynie jednym z wielu możliwych kodowań
    konstruktora [cons]. Inaczej możemy go zakodować np. tak: *)

Definition consW' {X : Type} (h : X) (t : listW X) : listW X :=
  sup (inr h) (fun u : unit => match u with | tt => t end).

(** Kodowania te nie są konwertowalne, ale jeżeli użyjemy aksjomatu
    ekstensjonalności dla funkcji, to możemy pokazać, że są równe. *)

Fail Check eq_refl : consW = consW'.
(* ===> The command has indeed failed with message:
        The term "eq_refl" has type "consW = consW"
        while it is expected to have type "consW = consW'". *)

Lemma consW_consW' :
  forall {X : Type} (h : X) (t : listW X),
    consW h t = consW' h t.
Proof.
  intros. unfold consW, consW'. f_equal.
  extensionality u. destruct u.
  reflexivity.
Qed.

(** Podobnym mykiem musimy posłużyć się, żeby udowodnić regułę indukcji.
    Dowód zaczynamy od indukcji po [l] (musimy pamiętać, że nasze [W] jest
    typem induktywnym, więc ma regułę indukcji), ale nie możemy bezpośrednio
    użyć hipotez [PnilW] ani [PconsW], gdyż dotyczą one innych kodowań [nil]
    i [cons] niż te, które pojawiają się w celu. Żeby uporać się z problemem,
    używamy taktyki [replace], a następnie dowodzimy, że obydwa kodowania są
    ekstensjoalnie równe. *)

Lemma listW_ind :
  forall
    (X : Type) (P : listW X -> Type)
    (PnilW : P (nilW X))
    (PconsW : forall (h : X) (t : listW X), P t -> P (consW h t)),
      forall l : listW X, P l.
Proof.
  induction l as [[[] | x] b IH].
    replace (P (sup (inl tt) b)) with (P (nilW X)).
      assumption.
      unfold nilW. do 2 f_equal. extensionality e. destruct e.
    replace _ with (P (consW x (b tt))).
      apply PconsW. apply IH.
      unfold consW. do 2 f_equal.
        extensionality u. destruct u. reflexivity.
Defined.

Lemma listW_ind' :
  forall
    (X : Type) (P : listW X -> Type)
    (PnilW : P (nilW X))
    (PconsW : forall (h : X) (t : listW X), P t -> P (consW h t)),
      {f : forall l : listW X, P l |
        f (nilW X) = PnilW /\
        forall (h : X) (t : listW X), f (consW h t) = PconsW h t (f t)}.
Proof.
  esplit. Unshelve.
    2: {
      induction l as [[[] | x] b IH].
        replace (P (sup (inl tt) b)) with (P (nilW X)).
          assumption.
          unfold nilW. do 2 f_equal. extensionality e. destruct e.
        replace _ with (P (consW x (b tt))).
          apply PconsW. apply IH.
          unfold consW. do 2 f_equal.
            extensionality u. destruct u. reflexivity.
    }
    cbn. split.
      compute. assert (forall (P : Prop) (p1 p2 : P), p1 = p2).
        admit.
Admitted.

(** Skoro mamy regułę indukcji, to bez problemu jesteśmy w stanie pokazać,
    że typy [list X] oraz [listW X] są izomorficzne, tzn. istnieją funkcje
    [f : list X -> listW X] oraz [g : listW X -> list X], które są swoimi
    odwrotnościami. *)

Fixpoint f {X : Type} (l : list X) : listW X :=
match l with
| nil => nilW X
| cons h t => consW h (f t)
end.

Definition g {X : Type} : listW X -> list X.
Proof.
  apply listW_ind'.
    exact nil.
    intros h _ t. exact (cons h t).
Defined.

Lemma fg :
  forall {X : Type} (l : list X),
    g (f l) = l.
Proof.
  induction l as [| h t].
    unfold g in *. destruct (listW_ind' _) as (g & eq1 & eq2).
      cbn. apply eq1.
    unfold g in *; destruct (listW_ind' _) as (g & eq1 & eq2).
      cbn. rewrite eq2, IHt. reflexivity.
Qed.

Lemma gf :
  forall {X : Type} (l : listW X),
    f (g l) = l.
Proof.
  intro.
  apply listW_ind';
  unfold g; destruct (listW_ind' _) as (g & eq1 & eq2).
    rewrite eq1. cbn. reflexivity.
    intros. rewrite eq2. cbn. rewrite H. reflexivity.
Qed.

Definition boolW : Type :=
  W bool (fun _ => Empty_set).

Definition trueW : boolW :=
  sup true (fun e : Empty_set => match e with end).

Definition falseW : boolW :=
  sup false (fun e : Empty_set => match e with end).

Definition notW : boolW -> boolW :=
  W_rect bool (fun _ => Empty_set) (fun _ => boolW)
         (fun b _ _ => if b then falseW else trueW).

Definition bool_boolW (b : bool) : boolW :=
  if b then trueW else falseW.

Definition boolW_bool : boolW -> bool :=
  W_rect bool (fun _ => Empty_set) (fun _ => bool) (fun b _ _ => b).

Lemma boolW_bool_notW :
  forall b : boolW,
    boolW_bool (notW b) = negb (boolW_bool b).
(* begin hide *)
Proof.
  induction b; cbn. destruct x; cbn; reflexivity.
Qed.
(* end hide *)

Lemma boolW_bool__bool_boolW :
  forall b : bool,
    boolW_bool (bool_boolW b) = b.
(* begin hide *)
Proof.
  destruct b; reflexivity.
Qed.
(* end hide *)

Lemma bool_boolW__bool_boolW :
  forall b : boolW,
    bool_boolW (boolW_bool b) = b.
(* begin hide *)
Proof.
  unfold bool_boolW, boolW_bool. destruct b, x; cbn.
    unfold trueW. f_equal. extensionality e. destruct e.
    unfold falseW. f_equal. extensionality e. destruct e.
Qed.
(* end hide *)

Definition natW : Type :=
  W bool (fun b : bool => if b then Empty_set else unit).

Definition zeroW : natW :=
  sup true (fun e : Empty_set => match e with end).

Definition succW (n : natW) : natW :=
  sup false (fun u : unit => n).

Definition doubleW : natW -> natW :=
  W_rect _ (fun b : bool => if b then Empty_set else unit) (fun _ => natW)
    (fun a =>
      match a with
      | true => fun _ _ => zeroW
      | false => fun _ g => succW (succW (g tt))
      end).

Definition natW_nat :=
  W_rect _ (fun b : bool => if b then Empty_set else unit) (fun _ => nat)
    (fun a =>
      match a with
      | true => fun _ _ => 0
      | false => fun _ g => S (g tt)
      end).

Fixpoint nat_natW (n : nat) : natW :=
match n with
| 0 => zeroW
| S n' => succW (nat_natW n')
end.

Lemma natW_nat_doubleW :
  forall n : natW,
    natW_nat (doubleW n) = 2 * natW_nat n.
(* begin hide *)
Proof.
  induction n. destruct x; cbn.
    reflexivity.
    rewrite H. cbn. rewrite <- !plus_n_O, plus_n_Sm. reflexivity.
Qed.
(* end hide *)

Lemma natW_nat__nat_natW :
  forall n : nat,
    natW_nat (nat_natW n) = n.
(* begin hide *)
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    rewrite IHn'. reflexivity.
Qed.
(* end hide *)

Lemma nat_natW__nat_natW :
  forall n : natW,
    nat_natW (natW_nat n) = n.
(* begin hide *)
Proof.
  induction n; destruct x; cbn.
    unfold zeroW. f_equal. extensionality e. destruct e.
    rewrite H. unfold succW. f_equal. extensionality u.
      destruct u. reflexivity.
Qed.
(* end hide *)

End listW.

(** **** Ćwiczenie *)

(** Napisałem we wstępie, że W-typy umożliwiają reprezentowanie dowolnych
    typów induktywnych, ale czy to prawda? Przekonajmy się!

    Zdefiniuj za pomocą [W] następujące typy i udowodnij, że są one
    izomorficzne z ich odpowiednikami:
    - [False] (czyli [Empty_set])
    - [unit]
    - [bool]
    - typ o [n] elementach
    - liczby naturalne
    - produkt
    - sumę

    Załóżmy teraz, że żyjemy w świecie, w którym nie ma typów induktywnych.
    Jakich typów, oprócz [W], potrzebujemy, by móc zdefiniować wszystkie
    powyższe typy? *)

(* begin hide *)

(* TODO *)

(** Odpowiedź: zdaje się, że potrzebujemy 0, 1, 2, *, + *)

Print W.

Definition FalseW : Type :=
  W False (fun _ => False).

Definition unitW : Type :=
  W unit (fun _ => False).

Definition boolW : Type :=
  W bool (fun _ => False).

Definition prodW (A B : Type) : Type :=
  W (A * B) (fun _ => False).

Definition sumW (A B : Type) : Type :=
  W (A + B) (fun _ => False).

Definition natW : Type :=
  W bool (fun b : bool => if b then False else unit).

Definition Fin (n : natW) : Type.
Proof.
  apply (W_rect _ _ (fun _ : natW => Type)).
    destruct x; intros.
      exact False.
      exact (option (X tt)).
    exact n.
Defined.

(* end hide *)

(** ** Indukcja w dwóch postaciach (TODO) *)

Module nat_ind.

(* begin hide *)
(*
TODO: dokończyć dowód indukcja = rekursja + unikalność
*)
(* end hide *)

Record recursive
  {A : Type} (f : nat -> A)
  (z : A) (s : A -> A) : Prop :=
{
    f_0 : f 0 = z;
    f_S : forall n : nat, f (S n) = s (f n);
}.

Fixpoint nat_rec'
  {A : Type} (z : A) (s : A -> A) (n : nat) : A :=
match n with
| 0 => z
| S n' => s (nat_rec' z s n')
end.

Theorem recursive_nat_rec' :
  forall 
    {A : Type} (z : A) (s : A -> A),
      recursive (nat_rec' z s) z s.
Proof.
  split; cbn; reflexivity.
Qed.

Definition recursor : Type :=
  forall
    (A : Type) (z : A) (s : A -> A),
      {f : nat -> A | recursive f z s}.

Definition uniqueness : Prop :=
  forall
    (A : Type) (f g : nat -> A)
    (z : A) (s : A -> A),
      recursive f z s -> recursive g z s ->
        forall n : nat, f n = g n.

Definition nat_ind' : Type :=
  forall
    (P : nat -> Type)
    (z : P 0) (s : forall n : nat, P n -> P (S n)),
      {f : forall n : nat, P n |
        (f 0 = z) /\
        (forall n : nat, f (S n) = s n (f n))
      }.

Theorem induction_recursor :
  nat_ind' -> recursor.
Proof.
  unfold nat_ind', recursor.
  intros ind A z s.
  destruct (ind (fun _ => A) z (fun _ => s)) as (f & f_0 & f_S).
  exists f.
  split; assumption.
Qed.

Theorem induction_uniqueness :
  nat_ind' -> uniqueness.
Proof.
  unfold nat_ind', uniqueness.
  intros ind A f g z s [f_0 f_S] [g_0 g_S].
  apply
  (
    ind
      (fun n => f n = g n)
  ).
    rewrite f_0, g_0. reflexivity.
    intros n Heq. rewrite f_S, g_S. f_equal. assumption.
Qed.

Theorem recursor_uniqueness_induction :
  recursor -> uniqueness -> nat_ind'.
Proof.
  unfold recursor, uniqueness, nat_ind'.
  intros rec uniqueness P z s. Print sigT.
  destruct
  (
    rec
      {n : nat & P n}
      (existT _ 0 z)
      (fun '(existT _ n p) => existT _ (S n) (s n p))
  )
  as (f & f_0 & f_S).
  assert (forall n : nat, projT1 (f n) = n).
    eapply (uniqueness nat (fun n => projT1 (f n)) (fun n => n)). Unshelve.
      4: exact 0.
      4: exact S.
      split.
        apply (f_equal (@projT1 nat P)) in f_0. cbn in f_0. assumption.
        intro. rewrite f_S. destruct (f n). cbn. reflexivity.
      split.
        reflexivity.
        reflexivity.
  esplit. Unshelve.
    2: { intro n. rewrite <- H. exact (projT2 (f n)). }
    cbn. split.
Admitted.

End nat_ind.

(** * Indeksowane W-typy (TODO) *)

(** Jak głosi pewna stara książka z Palestyny, nie samymi W-typami żyje
    człowiek. W szczególności, W-typy mogą uchwycić jedynie dość proste
    typy induktywne, czyli takie, które wspierają jedynie parametry oraz
    argumenty indukcyjne. Na chwilę obecną wydaje mi się też, że [W] nie
    jest w stanie reprezentować typów wzajemnie induktywnych, lecz pewny
    nie jest jestem.

    Trochę to smutne, gdyż naszą główną motywacją ku poznawaniu [W]-typów
    jest teoretyczne zrozumienie mechanizmu działania typów induktywnych,
    a skoro [W] jest biedne, to nie możemy za jego pomocą zrozumieć
    wszystkich typów induktywnych. Jednak uszy do góry, gdyż na ratunek w
    naszej misji przychodzą nam indeksowane W-typy!

    Co to za zwierzę, te indeksowane W-typy? Ano coś prawie jak oryginalne
    W, ale trochę na sterydach. Definicja wygląda tak: *)

Inductive IW
  (I : Type)
  (S : I -> Type)
  (P : forall (i : I), S i -> Type)
  (r : forall (i : I) (s : S i), P i s -> I)
  : I -> Type :=
| isup :
    forall (i : I) (s : S i),
      (forall p : P i s, IW I S P r (r i s p)) -> IW I S P r i.

Arguments isup {I S P r} _ _ _.

(** Prawdopodobnie odczuwasz w tej chwili wielką grozę, co najmniej jakbyś
    zobaczył samego Cthulhu. Nie martw się - zaraz dokładnie wyjasnimy, co
    tu się dzieje, a potem rozpracujemy indeksowane W typy na przykładach
    rodzin typów induktywnych, które powinieneś już dobrze znać.

    Objaśnienia:
    - [I : Type] to typ indeksów
    - [S i] to typ kształtów o indeksie [i]. Kształt to konstruktor wraz ze
      swoimi argumentami nieindukcyjnymi.
    - [P s] to typ mówiący, ile jest argumentów indukcyjnych o kształcie [s].
    - [r p] mówi, jak jest indeks argumentu indukcyjnego [p]. *)

(** Konstruktor [isup] mówi, że jeżeli mamy indeks i kształt dla tego
    indeksu, to jeżeli uda nam się zapchać wszystkie argumenty indukcyjne
    rzeczami o odpowiednim indeksie, to dostajemy element [IW ...] o takim
    indeksie jak chcieliśmy.

    Czas na przykład: *)

Inductive Vec (A : Type) : nat -> Type :=
| vnil : Vec A 0
| vcons : forall n : nat, A -> Vec A n -> Vec A (S n).

Arguments vcons {A n} _ _.

(** Na pierwszy ogień idzie [Vec], czyli listy indeksowane długością. Jak
    wygląda jego reprezentacja za pomocą [IW]? *)

Definition I_Vec (A : Type) : Type := nat.

(** Przede wszystkim musimy zauważyć, że typem indeksów [I] jest [nat]. *)

Definition S_Vec {A : Type} (i : I_Vec A) : Type :=
match i with
| 0 => unit
| S _ => A
end.

(** Typ kształtów definiujemy przez dopasowanie indeksu do wzorca, bo dla
    różnych indeksów mamy różne możliwe kształty. Konstruktor [vnil] jest
    jedynym konstruktorem o indeksie [0] i nie bierze on żadnych argumentów
    nieindukcyjnych, stąd w powyższej definicji klauzula [| 0 => unit].
    Konstruktor [vcons] jest jedynym konstruktorem o indeksie niezerowym i
    niezależnie od indeksu bierze on jeden argument nieindukcyjny typu [A],
    stąd klauzula [| S _ => A]. *)

Definition P_Vec {A : Type} {i : I_Vec A} (s : S_Vec i) : Type :=
match i with
| 0 => False
| S _ => unit
end.

(** Typ pozycji różwnież definiujemy przez dopasowanie indeksu do wzorca,
    bo różne kształty będą miały różne pozycje, a przecież kształty też są
    zdefiniowane przez dopasowanie indeksu. Konstruktor [vnil] nie bierze
    argumentów indukcyjnych i stąd klauzula [| 0 => False]. Konstruktor
    [vcons] bierze jeden argument indukcyjny i stąd klauzula [| S _ => unit].

    Zauważmy, że niebranie argumentu nieindukcyjnego reprezentujemy inaczej
    niż niebranie argumentu indukcyjnego.

    [vnil] nie bierze argumentów nieindukcyjnych, co w typie kształtów [S_Vec]
    reprezentujemy za pomocą typu [unit]. Możemy myśleć o tym tak, że [vnil]
    bierze jeden argument typu [unit]. Ponieważ [unit] ma tylko jeden element,
    to i tak z góry wiadomo, że będziemy musieli jako ten argument wstawić
    [tt].

    [vnil] nie bierze też argumentów indukcyjnych, co w typue pozycji [P_Vec]
    reprezentujemy za pomocą typu [False]. Możemy myśleć o tym tak, że jest
    tyle samo argumentów indukcyjnych, co dowodów [False], czyli zero.

    Podsumowując, różnica jest taka, że dla argumentów nieindukcyjnych typ
    [X] oznacza "weź element typu X", zaś dla argumentów indukcyjnych typ
    [X] oznacza "weź tyle elementów typu, który właśnie definiujemy, ile
    jest elementów typu X". *)

Definition r_Vec
  {A : Type} {i : I_Vec A} {s : S_Vec i} (p : P_Vec s) : I_Vec A.
Proof.
  destruct i as [| i']; cbn in p.
    destruct p.
    exact i'.
Defined.

(** Pozostaje nam tylko zdefiniować funkcję, która pozycjom argumentów
    indukcyjnym w poszczególnych kształtach przyporządkowuje ich indeksy.
    Definiujemy tę funkcję przez dowód, gdyż Coq dość słabo rodzi sobie z
    dopasowaniem do wzorca przy typach zależnych.

    Ponieważ kształty są zdefiniowane przez dopasowanie indeksu do wzorca,
    to zaczynamy od rozbicia indeksu na przypadki. Gdy indeks wynosi zero,
    to mamy do czynienia z reprezentacją konstruktora [vnil], który nie
    bierze żadnych argumentów indukcyjnych, co ujawnia się pod postacią
    sprzeczności. Gdy indeks wynosi [S i'], mamy do czynienia z konstruktorem
    [vcons i'], który tworzy element typu [Vec A (S i')], zaś bierze element
    typu [Vec A i']. Wobec tego w tym przypadku zwracamy [i']. *)

Definition Vec' (A : Type) : nat -> Type :=
  IW (I_Vec A) (@S_Vec A) (@P_Vec A) (@r_Vec A).

(** Tak wygląda ostateczna definicja [Vec'] - wrzucamy do [IW] odpowiednie
    indeksy, kształty, pozycje oraz funkcję przypisującą indeksy pozycjom.

    Spróbujmy przekonać się, że typy [Vec A n] oraz [Vec' A n] są
    izomorficzne. W tym celu musimy zdefiniować funkcje
    [f : Vec A n -> Vec' A n] oraz [g : Vec' A n -> Vec A n], które są
    swoimi odwrotnościami. *)

Fixpoint f {A : Type} {n : nat} (v : Vec A n) : Vec' A n.
Proof.
  destruct v.
    apply (isup 0 tt). cbn. destruct p.
    apply (@isup _ _ _ (@r_Vec A) (S n) a). cbn. intros _.
      exact (f _ _ v).
Defined.

(** Najłatwiej definiować nam będzie za pomocą taktyk. Definicja [f] idzie
    przez rekursję strukturalną po [v]. [isup 0 tt] to reprezentacja [vnil],
    zaś [@isup _ _ _ (@r_Vec A) (S n) a] to reprezentacja [vcons a]. Dość
    nieczytelne, prawda? Dlatego właśnie nikt w praktyce nie używa
    indeksowanych W-typów. *)

Fixpoint g {A : Type} {n : nat} (v : Vec' A n) : Vec A n.
Proof.
  destruct v as [[| i'] s p]; cbn in s.
    apply vnil.
    apply (vcons s). apply g. apply (p tt).
Defined.

(** W drugą stronę jest łatwiej. Definicja idzie oczywiście przez rekursję
    po [v] (pamiętajmy, że [Vec' A n] to tylko specjalny przypadek [IW],
    zaś [IW] jest induktywne). Po rozbiciu [v] na komponenty sprawdzamy,
    jaki ma ono indeks. Jeżeli [0], zwracamy [vnil]. Jeżeli niezerowy, to
    zwracamy [vcons] z głową [s] rekurencyjnie obliczonym ogonem. *)

Lemma f_g :
  forall {A : Type} {n : nat} (v : Vec A n),
    g (f v) = v.
Proof.
  induction v; cbn.
    reflexivity.
    rewrite IHv. reflexivity.
Qed.

(** Dowód odwrotności w jedną stronę jest banalny - indukcja po [v] idzie
    gładko, bo [v] jest typu [Vec A n]. *)

Require Import FunctionalExtensionality.

Lemma g_f :
  forall {A : Type} {n : nat} (v : Vec' A n),
    f (g v) = v.
Proof.
  induction v as [[| i'] s p IH]; unfold I_Vec in *; cbn in *.
    destruct s. f_equal. extensionality x. destruct x.
    f_equal. extensionality u. destruct u. apply IH.
Qed.

(** W drugę stronę dowód jest nieco trudniejszy. Przede wszystkim, musimy
    posłużyć się aksjomatem ekstensjonalności dla funkcji. Wynika to z faktu,
    że w [IW] reprezentujemy argumenty indukcyjne wszystkie na raz za pomocą
    pojedynczej funkcji.

    Zaczynamy przez indukcję po [v] i rozbijamy indeks żeby sprawdzić, z
    którym kształtem mamy do czynienia. Kluczowym krokime jest odwinięcie
    definicji [I_Vec] - bez tego taktyka [f_equal] nie zadziała tak jak
    powinna. W obu przypadkach kończymy przez użycie ekstensjonalności
    do udowodnienia, że argumenty indukcyjne są równe. *)

(** **** Ćwiczenie *)

(** Zdefiniuj za pomocą [IW] następujące predykaty/relacje/rodziny typów:
    - [even] i [odd]
    - typ drzew binarnych trzymających wartości w węzłach, indeksowany
      wysokością
    - to samo co wyżej, ale indeksowany ilością elementów
    - porządek [<=] dla liczb naturalnych
    - relację [Perm : list A -> list A -> Prop] mówiącą, że [l1] i [l2]
      są swoimi permutacjami *)

(** * M-typy (TODO) *)

(** M-typy to to samo co W-typy, tylko że dualne. Pozdro dla kumatych. *)

From Typonomikon Require Import F1.

(** Naszą motywacją do badania W-typów było to, że są one jedynym
    pierścieniem (w sensie Władcy Pierścieni, a nie algebry abstrakcyjnej),
    tj. pozwalają uchwycić wszystkie typy induktywne za pomocą jednego
    (oczywiście o ile mamy też [False], [unit], [bool], [prod] i [sum]).

    Podobnie możemy postawić sobie zadanie zbadania wszystkich typów
    koinduktywnych. Rozwiązanie zadania jest (zupełnie nieprzypadkowo)
    analogiczne do tego dla typów induktywnych, a są nim M-typy. Skąd nazwa?
    Zauważ, że M to nic innego jak W postawione na głowie - podobnie esencja
    M-typów jest taka sama jak W-typów, ale interpretacja jest postawiona
    na głowie. *)

CoInductive M (S : Type) (P : S -> Type) : Type :=
{
    shape : S;
    position : P shape -> M S P
}.

Arguments shape {S P}.
Arguments position {S P} _ _.

(** Zastanówmy się przez chwilę, dlaczego definicja [M] wygląda właśnie tak.
    W tym celu rozważmy dowolny typ koinduktywny [C] i przyjmijmy, że ma on
    pola [f1 : X1], ..., [fn : Xn]. Argumenty możemy podzielić na dwie grupy:
    koindukcyjne (których typem jest [C] lub funkcje postaci [B -> C]) oraz
    niekoindukcyjne (oznaczmy ich typy przez [A]).

    Oczywiście wszystkie niekoindukcyjne pola o typach [A1], ..., [Ak] możemy
    połączyć w jedno wielgachne pole o typie [A1 * ... * Ak] i tym właśnie
    jest występujące w [M] pole [shape]. Podobnie jak w przypadku W-typów,
    typ [S] będziemy nazywać typem kształtów.

    Pozostała nam jeszcze garść pól typu [C] (lub w nieco ogólniejszym
    przypadku, o typach [B1 -> C], ..., [Bn -> C]. Nie trudno zauważyć,
    że można połączyć je w typ [B1 + ... + Bn -> C]. Nie tłumaczy to
    jednak tego, że typ pozycji zależy od konkretnego kształtu.

    Źródeł można doszukiwać się w jeszcze jednej, nieco bardziej złożonej
    postaci destruktorów. Żeby za dużo nie mącić, rozważmy przykład. Niech
    [C] ma destruktor postaci [nat -> C + nat]. Jak dokodować ten destruktor
    do [shape] i [position]? Otóż dorzucamy do [shape] nowy komponent, czyli
    [shape' := shape * nat -> option nat].

    A psu w dupę z tym wszystkim. TODO *)

(* begin hide *)

Inductive Finite {S : Type} {P : S -> Type} : M S P -> Prop :=
| FiniteRec  :
    forall m : M S P,
      (forall p : P (shape m), Finite (position m p)) -> Finite m.

Set Warnings "-cannot-define-projection".
CoInductive Infinite {S : Type} {P : S -> Type} (m : M S P) : Prop :=
{
    p : P (shape m);
    Infinite' : Infinite (position m p);
}.
Set Warnings "cannot-define-projection".

(* TODO *) Lemma Finite_or_Infinite_irrefutable :
  forall {S : Type} {P : S -> Type} (m : M S P),
    ~ ~ (Finite m \/ Infinite m).
Proof.
  intros S P m H.
  apply H. right. revert m H. cofix CH.
  intros [s pos] H.
  econstructor; cbn.
  apply CH.
  intros [H' | H']; apply H.
    2: { right. econstructor; cbn. exact H'. }
    left. constructor. cbn. intro.
    exfalso. apply H. left. constructor. cbn. intro.
Abort.

Lemma Finite_Infinite_impossible :
  forall {S : Type} {P : S -> Type} {m : M S P},
    Finite m -> Infinite m -> False.
Proof.
  induction 1.
  intros [s inf].
  exact (H0 _ inf).
Qed.

(** Wtedy typ [c] wygląda tak:
    [c : A -> T * ... * T -> T]. Zauważmy, że [T * ... * T] możemy zapisać
    równoważnie jako [B -> T], gdzie [B] to typ mający tyle elementów, ile
    razy [T] występuje w produkcie [T * ... * T]. Zatem typ [c] przedstawia
    się tak: [c : A -> (B -> T) -> T].

    Teraz poczynimy kilka uogólnień. Po pierwsze, na początku założyliśmy,
    że [c] ma skończenie wiele argumentów indukcyjnych, ale postać [B -> T]
    uwzględnia także przypadek, gdy jest ich nieskończenie wiele (tzn. gdy
    [c] miał oryginalnie jakiś argument postaci [Y -> T] dla nieskończonego
    [Y]).

    Po drugie, założyliśmy, że [c] jest funkcją niezależną. Przypadek, gdy
    [c] jest funkcją zależną możemy pokryć, pozwalając naszemu [B] zależeć
    od [A], tzn. [B : A -> Type]. Typ konstruktora [c] zyskuje wtedy postać
    sumy zależnej [{x : A & B x -> T} -> T]. W ostatnim kroku odpakowujemy
    sumę i [c] zyskuje postać [c : forall x : A, B x -> T].

    Jak więc widać, typ każdego konstruktora można przekształcić tak, żeby
    móc zapisać go jako [forall x : A, B x -> T]. Zauważmy też, że jeżeli
    mamy dwa konstruktory [c1 : forall x : A1, B1 x -> T] oraz
    [c2 : forall x : A2, B2 x -> T], to możemy równie dobrze zapisać je
    za pomocą jednego konstruktora [c]: niech [A := A1 + A2] i niech
    [B (inl a1) := B1 a1, B (inl a2) := B2 a2]. Wtedy konstruktory [c1] i
    [c2] są równoważne konstruktorowi [c].

    Stosując powyższe przekształcenia możemy sprowadzić każdy typ induktywny
    do równoważnej postaci z jednym konstruktorem o typie
    [forall x : A, B x -> T]. Skoro tak, to definiujemy nowy typ, w którym
    [A] i [B] są parametrami... i bum, tak właśnie powstało [W]! *)

(* end hide *)

Definition transport
  {A : Type} {P : A -> Type} {x y : A} (p : x = y) (u : P x) : P y :=
match p with
| eq_refl => u
end.

CoInductive siM {S : Type} {P : S -> Type} (m1 m2 : M S P) : Prop :=
{
    shapes : shape m1 = shape m2;
    positions :
      forall p : P (shape m1),
        siM (position m1 p) (position m2 (transport shapes p))
}.

Definition P_Stream (A : Type) : A -> Type := fun _ => unit.

Definition Stream' (A : Type) : Type := M A (P_Stream A).

CoFixpoint ff {A : Type} (s : Stream A) : Stream' A :=
{|
    shape := hd s;
    position _ := ff (tl s);
|}.

CoFixpoint gg {A : Type} (s : Stream' A) : Stream A :=
{|
    hd := shape s;
    tl := gg (position s tt);
|}.

Lemma ff_gg :
  forall {A : Type} (s : Stream A),
    bisim (gg (ff s)) s.
Proof.
  cofix CH.
  constructor; cbn.
    reflexivity.
    apply CH.
Qed.

Lemma gg_ff :
  forall {A : Type} (s : Stream' A),
    siM (ff (gg s)) s.
Proof.
  cofix CH.
  econstructor. Unshelve.
    2: reflexivity.
    destruct p. cbn. apply CH.
Qed.

Definition coListM (A : Type) : Type :=
  M (option A) (fun x : option A =>
                match x with
                | None => False
                | Some _ => unit
                end).

CoFixpoint fff {A : Type} (l : coList A) : coListM A :=
match uncons l with
| None => {| shape := None; position := fun e : False => match e with end |}
| Some (h, t) => {| shape := Some h; position := fun _ => @fff _ t |}
end.

Print coBTree.

Definition coBTreeM (A : Type) : Type :=
  M (option A) (fun x : option A =>
                match x with
                | None => False
                | Some _ => bool
                end).

(** ** Ciekawostka: koindukcja i bipodobieństwo *)

(** TODO: regułę koindukcji można rozłożyć na regułę korekursji oraz
    regułę unikalności, a reguła unikalności sama w sobie w zasadzie
    oznacza, że bipodobieństwo to równość. *)

From Typonomikon Require F4.

Module uniqueness_bisim_eq.

Import F4.

Print Stream.
(* ===>
  CoInductive Stream (A : Type) : Type :=
  {
      hd : A;
      tl : Stream A
  }.
*)

Record corecursive
  {A X : Type} (f : X -> Stream A)
  (h : X -> A) (t : X -> X)
  : Prop :=
{
    hd_f : forall x : X, hd (f x) = h x;
    tl_f : forall x : X, tl (f x) = f (t x);
}.

CoFixpoint corec
  {A X : Type} (h : X -> A) (t : X -> X) (x : X) : Stream A :=
{|
    hd := h x;
    tl := corec h t (t x);
|}.

Lemma corecursive_corec :
  forall {A X : Type} (h : X -> A) (t : X -> X),
    corecursive (corec h t) h t.
Proof.
  split; cbn; intro.
    reflexivity.
    reflexivity.
Qed.

Definition uniqueness (A : Type) : Prop :=
  forall
    (X : Type) (f g : X -> Stream A)
    (h : X -> A) (t : X -> X),
      corecursive f h t -> corecursive g h t ->
        forall x : X, f x = g x.

Definition bisim_to_eq (A : Type) : Prop :=
  forall s1 s2 : Stream A, bisim s1 s2 -> s1 = s2.

Fixpoint nth {A : Type} (s : Stream A) (n : nat) : A :=
match n with
| 0 => hd s
| S n' => nth (tl s) n'
end.

Fixpoint drop {A : Type} (s : Stream A) (n : nat) : Stream A :=
match n with
| 0 => s
| S n' => drop (tl s) n'
end.

Lemma hd_drop :
  forall {A : Type} (n : nat) (s : Stream A),
    hd (drop s n) = nth s n.
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite IHn'. reflexivity.
Qed.

Lemma tl_drop :
  forall {A : Type} (n : nat) (s : Stream A),
    tl (drop s n) = drop s (S n).
Proof.
  induction n as [| n']; cbn; intros.
    reflexivity.
    rewrite IHn'. cbn. reflexivity.
Qed.

#[global] Hint Resolve hd_drop tl_drop : core.

Theorem coinduction :
  forall (A : Type),
    uniqueness A -> bisim_to_eq A.
Proof.
  unfold uniqueness, bisim_to_eq.
  intros A uniqueness s1 s2 Hsim.
  eapply (uniqueness nat (drop s1) (drop s2) (nth s2) S _ _ 0).
  Unshelve.
  all: repeat split; intro n; auto.
  revert s1 s2 Hsim.
  induction n as [| n']; cbn; intros.
    destruct Hsim. assumption.
    destruct Hsim. apply IHn'. assumption.
Qed.

Record tsim (A : Type) : Type :=
{
    t1 : Stream A;
    t2 : Stream A;
    sim : bisim t1 t2;
}.

Arguments t1  {A} _.
Arguments t2  {A} _.
Arguments sim {A} _.

Definition hd' {A : Type} (t : tsim A) : A :=
  hd (t2 t).

Definition tl' {A : Type} (t : tsim A) : tsim A :=
{|
    t1 := tl (t1 t);
    t2 := tl (t2 t);
    sim := tls _ _ (sim t);
|}.

Theorem coinduction' :
  forall (A : Type),
    uniqueness A -> bisim_to_eq A.
Proof.
  unfold uniqueness, bisim_to_eq.
  intros A uniqueness s1 s2 Hsim.
  eapply
  (
    uniqueness
      (tsim A) t1 t2 hd' tl'
      _ _
      {| t1 := s1; t2 := s2; sim := Hsim |}
  ).
  Unshelve.
  all: repeat split.
  destruct x, sim0. unfold hd'; cbn. assumption.
Qed.

End uniqueness_bisim_eq.

Module uniqueness_bisim_eq_general.

Record corecursive
  {S : Type} {P : S -> Type}
  {X : Type} (f : X -> M S P)
  (s : X -> S) (p : forall x : X, P (s x) -> X) : Prop :=
{
    shape_f :
      forall x : X, shape (f x) = s x;
    position_f :
      forall (x : X) (psx : P (shape (f x))),
        position (f x) psx = f (p x (transport (shape_f x) psx))
}.

CoFixpoint corec
  {S : Type} {P : S -> Type} {X : Type}
  (s : X -> S) (p : forall x : X, P (s x) -> X)
  (x : X) : M S P :=
{|
    shape := s x;
    position := fun psx : P (s x) => corec s p (p x psx)
|}.

Theorem corecursive_corec :
  forall
    {S : Type} {P : S -> Type}
    {X : Type} (s : X -> S) (p : forall x : X, P (s x) -> X),
      corecursive (corec s p) s p.
Proof.
  esplit.
  Unshelve. 
  all: cbn.
    2: reflexivity.
    cbn. reflexivity.
Qed.

Definition uniqueness (S : Type) (P : S -> Type) : Prop :=
  forall
    (X : Type) (f g : X -> M S P)
    (s : X -> S) (p : forall x : X, P (s x) -> X),
      corecursive f s p -> corecursive g s p ->
        forall x : X, f x = g x.

Definition sim_to_eq (S : Type) (P : S -> Type) : Prop :=
  forall m1 m2 : M S P, siM m1 m2 -> m1 = m2.

Record I (S : Type) (P : S -> Type) : Type :=
{
    L : M S P;
    R : M S P;
    path : siM L R;
}.

Arguments L    {S P} _.
Arguments R    {S P} _.
Arguments path {S P} _.

Definition shape'
  {S : Type} {P : S -> Type} (i : I S P) : S :=
    shape (L i).

Definition position'
  {S : Type} {P : S -> Type} (i : I S P) (p : P (shape' i)) : I S P :=
{|
    L := position (L i) p;
    R := position (R i) (transport (shapes _ _ (path i)) p);
    path := positions _ _ (path i) p;
|}.

Lemma transport_eq_sym :
  forall {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P y),
    @transport _ P _ _ p (transport (eq_sym p) u) = u.
Proof.
  destruct p. cbn. reflexivity.
Qed.

Theorem coinduction :
  forall {S : Type} {P : S -> Type},
    uniqueness S P -> sim_to_eq S P.
Proof.
  unfold uniqueness, sim_to_eq.
  intros S P uniqueness m1 m2 Hsim.
  eapply
  (
    uniqueness
      (I S P) L R
      shape' position'
      _ _
      {| L := m1; R := m2; path := Hsim |}
  ).
  Unshelve.
  all: esplit.
  Unshelve.
  all: unfold shape'; cbn in *; try reflexivity; intro i.
    cbn. reflexivity.
    2: { destruct i, path0. cbn. symmetry. assumption. }
    intro. destruct i, path0. cbn. rewrite transport_eq_sym.
      reflexivity.
Qed.

End uniqueness_bisim_eq_general.

(** * Indeksowane M-typy? (TODO) *)

(** Nie dla psa kiełbajsa. *)

(** * Najmniejsze i największe punkty stałe funktorów *)

(** TODO: To tylko wstępna notatka, trzeba porządnie wytłumaczyć co to punkt
    TODO: stały i tak dalej. Zamknąć też [Mu] i [Nu] w osobny moduł. *)

From Typonomikon Require Import D1 D5 F3 F4.

Unset Positivity Checking.

(** Jeżeli wyłączymy sprawdzanie ścisłej pozytywności możemy zdefiniować rodziny
    typów [Mu] i [Nu] (po polsku wymawiane "mi" i "ni"), które reprezentują
    najmniejszy i największy punkt stały funktora. Pisząc "funktor" mam na myśli
    byt o typie [Type -> Type], zaś jego punkt stały to typ [X], który spełnia
    [F X = X]. *)

Inductive Mu (F : Type -> Type) : Type :=
| In : F (Mu F) -> Mu F.

Arguments In {F} _.

(** Spójrzmy na [Mu]. Jego jedyny konstruktor [In] ustanawia izomorfizm między
    typami [F (Mu F)] oraz [Mu F], co oznacza, że [Mu F] faktycznie jest punktem
    stałym funktora [F]. [Mu] jest typem induktywnym, co gwarantuje nam, że ten
    punkt stały jest najmniejszym punktem stałym. *)

CoInductive Nu (F : Type -> Type) : Type :=
{
    Out : F (Nu F);
}.

Arguments Out {F} _.

(** Dla [Nu] wszystko działa dokładnie dualnie. Pole [Out] ustanawia izomorfizm
    między [Nu F] i [F (Nu F)], co czyni [Nu F] punktem stałym funktora [F].
    Ponieważ [Nu] jest koinduktywne, ten punkt stały jest największym punktem
    stałym. *)

Set Positivity Checking.

(** Jak możemy użyć [Mu] i [Nu] do definiowania odpowiednio typów induktywnych
    i koinduktywnych? To proste: wystarczy zdefiniować funktor i zaaplikować do
    niego [Mu] lub [Nu]. Do definiowania funktorów najprościej zaś jest użyć
    mechanizmu definiowania typów induktywnych. *)

Inductive ListR (A X : Type) : Type :=
| NilR  : ListR A X
| ConsR : A -> X -> ListR A X.

Arguments NilR  {A X}.
Arguments ConsR {A X} _ _.

(** Typ [ListR] reprezentuje funktor wielomianowy [F(X) = 1 + A * X]. Jest to
    funktor bazowy typów [list] i [CoList], czyli że [list = Mu (ListR A)], a
    [CoList = Nu (ListR A)].

    Przyjrzyjmy się ze szczegółami, jak to dokładnie działa. *)

Module List.

Definition List (A : Type) : Type := Mu (ListR A).

(** Zdefiniowanie typu [List] jest banalne... *)

Unset Guard Checking.
Lemma List_ind' :
  forall
    {A : Type} (P : List A -> Prop)
    (HNil : P (In NilR))
    (HCons : forall (h : A) (t : List A), P t -> P (In (ConsR h t)))
    (l : List A), P l.
Proof.
  fix IH 5.
  destruct l as [[| h t]].
    exact HNil.
    apply HCons, IH; assumption.
Defined.
Set Guard Checking.

(** ... ale żeby udowodnić dla typu [List] regułę indukcji musimy wyłączyć
    termination checker. Powód tego jest prosty: [Mu] nie jest typem ściśle
    pozytywnym, a zatem Coq nie widzi, że nasza definicja faktycznie terminuje. *)

Fixpoint f {A : Type} (l : list A) : List A :=
match l with
| [] => In NilR
| h :: t => In (ConsR h (f t))
end.

(** Możemy łatwo przekształcić starą dobrą listę typu [list A] (który jest
    "zwykłym" typem induktywnym) w nową listę typu [List A] (tego zdefiniowanego
    za pomocą [Mu]. *)

Unset Guard Checking.
Fixpoint g {A : Type} (l : List A) {struct l} : list A :=
match l with
| In NilR        => []
| In (ConsR h t) => h :: g t
end.
Set Guard Checking.

(** Ale żeby przekształcić listę typu [List A] w listę typu [list A], musimy
    znowu wyłączyć termination checker (albo użyć reguły indukcji, której
    zdefiniowane również wymagało wyłączenia go). *)

Lemma fg :
  forall {A : Type} (l : list A),
    g (f l) = l.
Proof.
  induction l as [| h t]; cbn;
  rewrite ?IHt; reflexivity.
Qed.

Lemma gf :
  forall {A : Type} (l : List A),
    f (g l) = l.
Proof.
  intros.
  induction l using List_ind'; cbn.
    reflexivity.
    rewrite IHl. reflexivity.
Qed.

(** Udowodnienie, że typy [list A] i [List A] są izomorficzne jest bardzo łatwe,
    ale cały proces jest mocno dołujący, gdyż wymaga oszukania najpierw positivity
    checkera, a potem termination checkera *)

End List.

(** Niestety, to nie drobne oszustwa są naszym największym problemem (kto nigdy
    nie nakłamał babci, że wszystko jest ok?). Problem jest znacznie bardziej
    poważny: [Mu] oraz [Nu] umożliwiają nam udowodnienie fałszu.

    Jest tak dlatego, że typy w ogólności induktywne są punktami stałymi ściśle
    pozytywnych funktorów wielomianowych, podczas gdy do [Mu] możemy wstawić
    dowolny funktor. Podobnie sprawa ma się z [Nu].

    Zobaczmy, jak to wygląda w praktyce. *)

Inductive WutR (X : Type) : Type :=
| wutR : (X -> bool) -> WutR X.

Arguments wutR {X} _.

Definition Wut : Type := Mu WutR.

Definition wut (f : Wut -> bool) : Wut :=
  In (wutR f).

(** Widzieliśmy już w rozdziale o typach induktywnych, że negatywne typy
    induktywne prowadzą do sprzeczności. Właśnie tego faktu użyjemy by
    pokazać, że [Mu] również prowadzi do sprzeczności.

    Przykładem negatywnego typu induktywnego jest typ [Wut], który spełnia
    równanie [Wut = (Wut -> bool)]. Mając [Mu], możemy zdefiniować Wut] jako
    najmniejszy punkt stały funktora [F(X) = (X -> bool)] (który nazwaliśmy
    [wutR]). *)

Definition tuw (w : Wut) : Wut -> bool :=
match w with
| In (wutR f) => f
end.

(** Będziemy chcieli skorzystać z twierdzenia Cantora, więc potrzebna nam
    będzie funkcja typu [Wut -> Wut -> bool]. Zdefiniowanie takiej funkcji
    jest proste - każde [w : Wut] ma w środku funkcję [Wut -> bool]. *)

Lemma surjective_tuw :
  surjective tuw.
Proof.
  unfold Wut, surjective.
  intro f. exists (In (wutR f)).
  cbn. reflexivity.
Qed.

(** Funkcja [tuw] jest surjekcją - ponieważ każdą funkcję [Wut -> bool] można
    za pomocą konstruktora [wut] "włożyć" do typu [Wut], to każdą taką funkcję
    można również wyjąć z jakiegoś elementu typu [Wut]. *)

Lemma not_surjective_tuw :
  ~ surjective tuw.
Proof.
  apply (Cantor' tuw negb).
  destruct b; inversion 1.
Qed.

(** Ale twierdzenie Cantora mówi nam, że [tuw] nie możemy być surjekcją - typ
    funkcji z [Wut] w [bool] jest "większy" niż typ [Wut]. *)

Lemma Mu_illegal : False.
Proof.
  apply not_surjective_tuw.
  apply surjective_tuw.
Qed.

(** Ponieważ [tuw] jednocześnie jest i nie jest surjekcją, dostajemy sprzeczność
    i jes pozamiatane - typ [Mu] jest nielegalny. *)

Definition CoWut : Type := Nu WutR.

Definition tuw' (x y : CoWut) : bool :=
match Out x with
| wutR f => f y
end.

Lemma surjective_tuw' :
  surjective tuw'.
Proof.
  unfold surjective.
  intro f. exists {| Out := wutR f |}.
  unfold tuw'. cbn. reflexivity.
Qed.

Lemma not_surjective_tuw' :
  ~ surjective tuw'.
Proof.
  apply (Cantor' tuw' negb).
  destruct b; inversion 1.
Qed.

Lemma Nu_illegal : False.
Proof.
  apply not_surjective_tuw'.
  apply surjective_tuw'.
Qed.

(** Sprawa z [Nu] ma się zupełnie dualnie. Definiujemy typ [CoWut], który jest
    dualny do [Wut], tzn. jest największym punktem stałym funktora [WutR]. Mając
    element [w : CoWut] możemy z niego wyjąć dowolną funkcję [CoWut -> bool], a
    zatem mamy surjekcję [CoWut -> CoWut -> bool]. Z twierdzenia Cantora wiemy
    jednak, że jest to niemożliwe, a zatem mamy sprzeczność.

    Skoro wiemy już, że [Mu] i [Nu] nie są dobrym pomysłem, spróbujmy za Tym razem bez oszukiwania  *)

Module List'.

Inductive List (A : Type) : Type :=
| In : ListR A (List A) -> List A.

Arguments In {A} _.

(** Dużo lepiej jest "zawiązać węzeł" (w ten sposób często nazywane bywają
    techniki oparte o punkty stałe) ręcznie, bez używania [Mu] ani [Nu], dzięki
    czemu nie musimy oszukiwać i wyłączać positivity/termination checkera. Żeby
    to zrobić, wystarczy zdefiniować typ wyglądający jak [Mu]/[Nu], ale za to z
    podstawionym za [F] konkretnym funktorem.

    To właśnie robimy w powyższej, alternatywnej definicji typu [List A]: mamy
    jeden konstruktor [In], jak w [Mu], ale zamiast [F (Mu F)] bierze on dużo
    bardziej konkretny argument o typie [ListR A (List A)]. Dzięki temu Coq
    akceptuje powyższy typ jako poprawny. *)

Lemma List_ind' :
  forall
    {A : Type} (P : List A -> Prop)
    (HNil : P (In NilR))
    (HCons : forall (h : A) (t : List A), P t -> P (In (ConsR h t)))
    (l : List A), P l.
Proof.
  fix IH 5.
  destruct l as [[| h t]].
    exact HNil.
    apply HCons, IH; assumption.
Defined.

(** Teraz regułę indukcji możemy udowodnić bez większych problemów oraz bez
    oszukiwania. *)

Fixpoint f {A : Type} (l : list A) : List A :=
match l with
| [] => In NilR
| h :: t => In (ConsR h (f t))
end.

Fixpoint g {A : Type} (l : List A) : list A :=
match l with
| In NilR => []
| In (ConsR h t) => h :: g t
end.

(** Także funkcja zamieniająca nową listę w starę nie wymaga żadnych oszustw -
    możemy teraz normalnie programować z wykorzystaniem dopasowań i rekursji,
    nie musząc się martwić o termination checker. *)

Lemma fg :
  forall {A : Type} (l : list A),
    g (f l) = l.
Proof.
  induction l as [| h t]; cbn;
  rewrite ?IHt; reflexivity.
Qed.

Lemma gf :
  forall {A : Type} (l : List A),
    f (g l) = l.
Proof.
  intros.
  induction l using List_ind'; cbn.
    reflexivity.
    rewrite IHl. reflexivity.
Qed.

(** Dowody pozostają równie proste jak poprzednio. *)

End List'.

(** * Funktory bazowe często używanych typów *)

(** ** Zwykłe typy induktywne *)

(** Z wiedzą, którą dotychczas zdobyliśmy, nie trudno wyobrazić sobie, jak wygląda
    funktor bazowy typu [nat]. *)

Module NatF.

Inductive NatF (X : Type) : Type :=
| Zero : NatF X
| Succ : X -> NatF X.

Arguments Zero {X}.
Arguments Succ {X} _.

Inductive Nat : Type :=
| In : NatF Nat -> Nat.

Fixpoint f (n : nat) : Nat :=
match n with
| 0 => In Zero
| S n' => In (Succ (f n'))
end.

Fixpoint g (n : Nat) : nat :=
match n with
| In Zero => 0
| In (Succ n') => S (g n')
end.

Lemma fg :
  forall n : nat,
    g (f n) = n.
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    f_equal. assumption.
Qed.

Lemma gf :
  forall n : Nat,
    f (g n) = n.
Proof.
  fix IH 1.
  destruct n as [[| n']]; cbn.
    reflexivity.
    do 2 f_equal. apply IH.
Qed.

End NatF.

(** ** Typy sparametryzowane *)

(** Widzieliśmy już funktor bazowy dla list, rzućmy więc jeszcze szybko okiem
    na funkctor bazowy typu drzew binarnych. *)

Module BTree.

Inductive BTree (A : Type) : Type :=
| E : BTree A
| N : A -> BTree A -> BTree A -> BTree A.

Arguments E {A}.
Arguments N {A} _ _ _.

Module BTreeR.

Inductive BTreeR (A R : Type) : Type :=
| ER : BTreeR A R
| NR : A -> R -> R -> BTreeR A R.

Arguments ER {A R}.
Arguments NR {A R} _ _ _.

Inductive BTree' (A : Type) : Type :=
| In : BTreeR A (BTree' A) -> BTree' A.

Arguments In {A} _.

Fixpoint f {A : Type} (t : BTree A) : BTree' A :=
match t with
| E       => In ER
| N v l r => In (NR v (f l) (f r))
end.

Fixpoint g {A : Type} (t : BTree' A) : BTree A :=
match t with
| In ER         => E
| In (NR v l r) => N v (g l) (g r)
end.

Lemma fg :
  forall {A : Type} (t : BTree A), g (f t) = t.
Proof.
  induction t; cbn.
    reflexivity.
    rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma gf :
  forall {A : Type} (t : BTree' A), f (g t) = t.
Proof.
  fix IH 2.
  destruct t as [[]]; cbn.
    reflexivity. rewrite !IH. reflexivity.
Qed.

End BTreeR.

(** W środowiskach Haskellowych powyższy sposób definiowania funktorów bazowych
    zawie się "schematami rekursji". W Coqu możliwy jest też nieco inny sposób,
    który zobaczymy poniżej. *)

Module BTreeF.

Inductive BTreeF (F : Type -> Type) (A : Type) : Type :=
| EF : BTreeF F A
| NF : A -> F A -> F A -> BTreeF F A.

Arguments EF {F A}.
Arguments NF {F A} _ _ _.

(** Tym razem naszymi parametrami nie są już dwa typy [A] i [R], lecz funktor
    [F : Type -> Type] oraz typ [A]. Przez to poddrzewa reprezentujemy jako
    [F A] zamiast [R]. Poza tymi dwa drobnymi różnicami, wszystko inne pozostaje
    niezmienione. *)

Inductive BTree' (A : Type) : Type :=
| In : BTreeF BTree' A -> BTree' A.

Arguments In {A} _.

Fixpoint f {A : Type} (t : BTree A) : BTree' A :=
match t with
| E       => In EF
| N v l r => In (NF v (f l) (f r))
end.

Fixpoint g {A : Type} (t : BTree' A) : BTree A :=
match t with
| In EF => E
| In (NF v l r) => N v (g l) (g r)
end.

Lemma fg :
  forall {A : Type} (t : BTree A), g (f t) = t.
Proof.
  induction t; cbn.
    reflexivity.
    rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma gf :
  forall {A : Type} (t : BTree' A), f (g t) = t.
Proof.
  fix IH 2.
  destruct t as [[]]; cbn.
    reflexivity. rewrite !IH. reflexivity.
Qed.

End BTreeF.

End BTree.

(** ** Mutual inductive types *)

Module FinitaryTreeF.

Inductive Tree (A : Type) : Type :=
| Empty : Tree A
| Node  : A -> Forest A -> Tree A

with Forest (A : Type) : Type :=
| Nil  : Forest A
| Cons : Tree A -> Forest A -> Forest A.

Arguments Empty {A}.
Arguments Node  {A} _ _.

Arguments Nil   {A}.
Arguments Cons  {A} _ _.

Inductive TreeR (A F : Type) : Type :=
| EmptyR : TreeR A F
| NodeR  : A -> F -> TreeR A F.

Inductive ForestR (A F T : Type) : Type :=
| NilR  : ForestR A F T
| ConsR : T -> F -> ForestR A F T.

Arguments EmptyR {A F}.
Arguments NodeR  {A F} _ _.

Arguments NilR   {A F T}.
Arguments ConsR  {A F T} _ _.

Module TreeR.

Inductive Tree' (A : Type) : Type :=
| InT : TreeR A (Forest' A) -> Tree' A

with Forest' (A : Type) : Type :=
| InF : ForestR A (Forest' A) (Tree' A) -> Forest' A.

Arguments InT {A} _.

Arguments InF {A} _.

Fixpoint f {A : Type} (t : Tree A) : Tree' A :=
match t with
| Empty     => InT EmptyR
| Node x ts => InT (NodeR x (fs ts))
end

with fs {A : Type} (ts : Forest A) : Forest' A :=
match ts with
| Nil        => InF NilR
| Cons t ts' => InF (ConsR (f t) (fs ts'))
end.

Fixpoint g {A : Type} (t : Tree' A) : Tree A :=
match t with
| InT EmptyR       => Empty
| InT (NodeR x ts) => Node x (gs ts)
end

with gs {A : Type} (ts : Forest' A) : Forest A :=
match ts with
| InF NilR  => Nil
| InF (ConsR t ts') => Cons (g t) (gs ts')
end.

Lemma fg :
  forall {A : Type} (t : Tree A),
    g (f t) = t

with fsgs :
  forall {A : Type} (ts : Forest A),
    gs (fs ts) = ts.
Proof.
  destruct t as [| x ts]; cbn.
    reflexivity.
    rewrite fsgs. reflexivity.

  destruct ts as [| t ts']; cbn.
    reflexivity.
    rewrite fg, fsgs. reflexivity.
Qed.

Lemma gf :
  forall {A : Type} (t : Tree' A),
    f (g t) = t

with gsfs :
  forall {A : Type} (ts : Forest' A),
    fs (gs ts) = ts.
Proof.
  destruct t as [[| x ts]]; cbn.
    reflexivity.
    rewrite gsfs. reflexivity.

  destruct ts as [[| t ts']]; cbn.
    reflexivity.
    rewrite gf, gsfs. reflexivity.
Qed.

End TreeR.

Module TreeF.

Inductive TreeF (F : Type -> Type) (A : Type) : Type :=
| EmptyF : TreeF F A
| NodeF  : A -> F A -> TreeF F A.

Inductive ForestF (T F : Type -> Type) (A : Type) : Type :=
| NilF  : ForestF T F A
| ConsF : T A -> F A -> ForestF T F A.

Arguments EmptyF {F A}.
Arguments NodeF  {F A} _ _.

Arguments NilF   {T F A}.
Arguments ConsF  {T F A} _ _.

Inductive Tree' (A : Type) : Type :=
| InT : TreeF Forest' A -> Tree' A

with Forest' (A : Type) : Type :=
| InF : ForestF Tree' Forest' A -> Forest' A.

Arguments InT {A} _.

Arguments InF {A} _.

Fixpoint f {A : Type} (t : Tree A) : Tree' A :=
match t with
| Empty     => InT EmptyF
| Node x ts => InT (NodeF x (fs ts))
end

with fs {A : Type} (ts : Forest A) : Forest' A :=
match ts with
| Nil        => InF NilF
| Cons t ts' => InF (ConsF (f t) (fs ts'))
end.

Fixpoint g {A : Type} (t : Tree' A) : Tree A :=
match t with
| InT EmptyF       => Empty
| InT (NodeF x ts) => Node x (gs ts)
end

with gs {A : Type} (ts : Forest' A) : Forest A :=
match ts with
| InF NilF  => Nil 
| InF (ConsF t ts') => Cons (g t) (gs ts')
end.

Lemma fg :
  forall {A : Type} (t : Tree A),
    g (f t) = t

with fsgs :
  forall {A : Type} (ts : Forest A),
    gs (fs ts) = ts.
Proof.
  destruct t as [| x ts]; cbn.
    reflexivity.
    rewrite fsgs. reflexivity.

  destruct ts as [| t ts']; cbn.
    reflexivity.
    rewrite fg, fsgs. reflexivity.
Qed.

Lemma gf :
  forall {A : Type} (t : Tree' A),
    f (g t) = t

with gsfs :
  forall {A : Type} (ts : Forest' A),
    fs (gs ts) = ts.
Proof.
  destruct t as [[| x ts]]; cbn.
    reflexivity.
    rewrite gsfs. reflexivity.

  destruct ts as [[| t ts']]; cbn.
    reflexivity.
    rewrite gf, gsfs. reflexivity.
Qed.

End TreeF.

End FinitaryTreeF.

(** ** Indexed families *)

Require Import List.
Import ListNotations.

From Typonomikon Require Import F3 F4.

Module ListCoList.

Module CoList.

Import F4.

Module CoList_ForallF.

Inductive ForallF
  {A : Type} (R : A -> A -> Prop)
  (F : (A -> A -> Prop) -> CoList A -> CoList A -> Prop)
  : CoList A -> CoList A -> Prop :=
| Nils  :
    forall l1 l2 : CoList A,
      uncons l1 = NilF -> uncons l2 = NilF -> ForallF R F l1 l2
| Conss :
    forall (l1 l2 : CoList A) (h1 h2 : A) (t1 t2 : CoList A),
      uncons l1 = ConsF h1 t1 -> uncons l2 = ConsF h2 t2 ->
        R h1 h2 -> F R t1 t2 -> ForallF R F l1 l2.

CoInductive CoForall {A : Type} (R : A -> A -> Prop) (l1 l2 : CoList A) : Prop :=
{
    uncons' : ForallF R CoForall l1 l2
}.

End CoList_ForallF.

End CoList.

End ListCoList.

(** ** Indexed families, but reduced to parameterized types through equality constraints *)

Module ListCoList2.

Inductive ListR (A R : Type) : Type :=
| NilR  : ListR A R
| ConsR : A -> R -> ListR A R.

Arguments NilR  {A R}.
Arguments ConsR {A R} _ _.

Inductive List (A : Type) : Type :=
| In : ListR A (List A) -> List A.

Arguments In {A} _.

CoInductive CoList (A : Type) : Type :=
{
    uncons : ListR A (CoList A);
}.

Arguments uncons {A} _.

(** We can halve the amount of work to define many useful type families by just
    reusing templates operating on the "underlying functor", like below. *)

Inductive ForallR
  {A R : Type}
  (Unwrap : R -> ListR A R)
  (RA : A -> A -> Prop)
  (RR : R -> R -> Prop)
  (l1 l2 : R)
  : Prop :=
| Nils  :
    Unwrap l1 = NilR -> Unwrap l2 = NilR -> ForallR Unwrap RA RR l1 l2
| Conss :
    forall (h1 h2 : A) (t1 t2 : R),
      Unwrap l1 = ConsR h1 t1 -> Unwrap l2 = ConsR h2 t2 ->
        RA h1 h2 -> RR t1 t2 -> ForallR Unwrap RA RR l1 l2.

Definition uncons' {A : Type} (l : List A) : ListR A (List A) :=
match l with
| In x => x
end.

Inductive Forall {A : Type} (R : A -> A -> Prop) (l1 l2 : List A) : Prop :=
| InForall : ForallR uncons' R (Forall R) l1 l2 -> Forall R l1 l2.

CoInductive CoForall {A : Type} (R : A -> A -> Prop) (l1 l2 : CoList A) : Prop :=
{
    uncons'' : ForallR uncons R (CoForall R) l1 l2
}.

Inductive ExistsR
  {A L : Type}
  (Uncons : L -> ListR A L)
  (RA : A -> A -> Prop)
  (RL : L -> L -> Prop)
  (l1 l2 : L)
  : Prop :=
| Here  :
    forall (h1 h2 : A) (t1 t2 : L),
      Uncons l1 = ConsR h1 t1 -> Uncons l2 = ConsR h2 t2 ->
        RA h1 h2 -> ExistsR Uncons RA RL l1 l2
| There :
    forall (h1 h2 : A) (t1 t2 : L),
      Uncons l1 = ConsR h1 t1 -> Uncons l2 = ConsR h2 t2 ->
        RL t1 t2 -> ExistsR Uncons RA RL l1 l2.

Inductive Exists {A : Type} (R : A -> A -> Prop) (l1 l2 : List A) : Prop :=
| InExists : ExistsR uncons' R (Exists R) l1 l2 -> Exists R l1 l2.

Inductive CoExists {A : Type} (R : A -> A -> Prop) (l1 l2 : CoList A) : Prop :=
| InCoExists : ExistsR uncons R (CoExists R) l1 l2 -> CoExists R l1 l2.

(** Maybe we can define generic functions? *)

Fixpoint cata {A R : Type} (f : ListR A R -> R) (l : List A) : R :=
match l with
| In NilR        => f NilR
| In (ConsR h t) => f (ConsR h (cata f t))
end.

CoFixpoint ana {A R : Type} (f : R -> ListR A R) (r : R) : CoList A :=
{|
    uncons :=
      match f r with
      | NilR      => NilR
      | ConsR h t => ConsR h (ana f t)
      end
|}.

End ListCoList2.

(** * Kody (nie, nie do gier) *)

(** Innym pomysłem na jednorodne reprezentowanie typów induktywnych,
    trochę podobnym do W-typów, jest stworzenie uniwersum nazw (czyli
    kodów), które następnie będziemy mogli zinterpretować jako typy
    induktywne. *)

Inductive I : Type :=
| u : I
| nonind : forall A : Type, (A -> I) -> I
| ind : I -> I.

Fixpoint Arg (i : I) (X : Type) : Type :=
match i with
| u => unit
| nonind A f => {a : A & Arg (f a) X}
| ind i => X * Arg i X
end.

Definition iprod (A B : Type) : I :=
  nonind A (fun _ => nonind B (fun _ => u)).

Compute Arg (iprod nat bool) False.

Definition isum (A B : Type) : I :=
  nonind bool (fun b => nonind (if b then A else B) (fun _ => u)).

Compute Arg (isum nat bool) False.

Definition inat : I :=
  nonind bool (fun b => if b then u else ind u).

Compute Arg inat False.

Definition inat_nat {X : Type} (a : Arg inat X) : unit + X.
Proof.
  cbn in a. destruct a as [[] []].
    left. exact tt.
    right. exact x.
Defined.

Definition ilist (A : Type) : I :=
  nonind bool (fun b => if b then u else nonind A (fun _ => ind u)).

Compute Arg (ilist nat) False.

Definition ifalse : I := ind u.

Compute Arg ifalse unit.

Unset Positivity Checking.
Inductive IType (i : I) : Type :=
| intro : Arg i (IType i) -> IType i.
Set Positivity Checking.

(*
Fixpoint IType_ind
  {i : I}
  {P : IType i -> Type}
  (intro' : forall a : Arg i (IType i), P (intro a) ->
*)

Definition iinat := IType inat.

Definition Z : iinat.
Proof.
  constructor. cbn. exists true. cbn. exact tt.
Defined.

Definition iS (n : iinat) : iinat.
Proof.
  constructor. cbn. exists false. cbn. split.
    exact n.
    constructor.
Defined.

Unset Guard Checking.
Fixpoint iinat_ind
  {P : iinat -> Type}
  (z : P Z)
  (s : forall n : iinat, P n -> P (iS n))
  (n : iinat) {struct n} : P n.
Proof.
  destruct n as [[[] []]].
    exact z.
    destruct a. apply s. apply iinat_ind; assumption.
Qed.
Set Guard Checking.

Fixpoint nat_to_iinat (n : nat) : iinat :=
match n with
| 0 => Z
| S n' => iS (nat_to_iinat n')
end.

Definition pred (n : iinat) : option iinat :=
match n with
| intro _ (existT _ true _) => None
| intro _ (existT _ false (n', _)) => Some n'
end.

(*
Fixpoint iinat_to_nat (n : iinat) : nat :=
match pred n with
| None => 0
| Some n' => S (iinat_to_nat n')
end.
*)

Unset Guard Checking.
Fixpoint iinat_to_nat (n : iinat) : nat :=
match n with
| intro _ (existT _ true _) => 0
| intro _ (existT _ false (n', _)) => S (iinat_to_nat n')
end.
Set Guard Checking.

Lemma one_way :
  forall n : nat, iinat_to_nat (nat_to_iinat n) = n.
Proof.
  induction n as [| n']; cbn.
    reflexivity.
    f_equal. assumption.
Defined.

Compute one_way 0.

Lemma second_way' :
  forall n : iinat, nat_to_iinat (iinat_to_nat n) = n.
Proof.
  apply iinat_ind; cbn.
    reflexivity.
    intros n' IH. f_equal. assumption.
Qed.

Unset Guard Checking.
Fixpoint second_way
  (n : iinat) : nat_to_iinat (iinat_to_nat n) = n.
Proof.
  destruct n as [[[] []]]; cbn.
    reflexivity.
    unfold iS. repeat f_equal.
      apply second_way.
      destruct a. reflexivity.
Defined.
Set Guard Checking.

Compute second_way (iS Z).
Compute second_way (iS (iS Z)).

(** ** Kody dla typów induktywno-rekursywnych *)

Inductive IR (D : Type) : Type :=
| iota  : D -> IR D
| sigma : forall A : Type, (A -> IR D) -> IR D
| delta : forall A : Type, ((A -> D) -> IR D) -> IR D.

(** * Reprezentacja typów induktywnych za pomocą kontenerów *)

(** [S] to skrót od "shape", czyli po naszemu "kształt", zaś [P] ma przywodzić
    na myśl "position", czyli "pozycja". *)

Inductive Container (S : Type) (P : S -> Type) (X : Type) : Type :=
| ctain : forall s : S, (P s -> X) -> Container S P X.

Arguments ctain {S P X} _ _.

(* Definition Container (S : Type) (P : S -> Type) : Type -> Type :=
  fun X : Type => {s : S & P s -> X}. *)

Require Import List.
Import ListNotations.

Require Import Fin.
Require Import Equality.

Require Import Recdef.

Module CList.

Definition CList (A : Type) :=
  Container nat Fin.t A.

Definition prev {n : nat} (f : Fin.t (S (S n))) : Fin.t (S n).
Proof.
  inversion f as [| n' f'].
    exact F1.
    exact f'.
Defined.

Fixpoint f {A : Type} (l : list A) : CList A.
refine (
match l with
| [] => ctain 0 (fun s : Fin.t 0 => match s with end)
| x :: xs =>
  match f _ xs with
  | ctain n p => ctain (S n) _
  end
end).
  destruct n as [| n']; intro s.
    exact x.
    exact (p (prev s)).
Defined.
Definition g {A : Type} (c : CList A) : list A.
Proof.
  destruct c as [n p].
  revert n p.
  fix IH 1; intros [| n'] p.
    exact [].
    exact (p F1 :: IH _ (fun s => p (FS s))).
Defined.

Lemma fg :
  forall {A : Type} (l : list A),
    g (f l) = l.
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    revert h IHt.
    induction t as [| h' t']; cbn; intros.
      reflexivity.
      destruct (f t'). cbn in *. destruct s.
Abort.

Lemma gf :
  forall {A : Type} (c : CList A),
    f (g c) = c.
Proof.
  intros A [n p].
  induction n as [| n'].
    cbn. f_equal. admit.
    cbn. destruct (f _) eqn: Heq. destruct s.
      admit.
      destruct n' as [| n''].
        cbn in *. congruence.
        cbn in Heq.
Abort.

End CList.