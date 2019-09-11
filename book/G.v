(** * G: Inne spojrzenia na typy induktywne i koinduktywne *)

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

    Nie są one zbyt przydatne w praktyce, gdyż wszystko, co można za ich
    pomocą osiągnąć, można też osiągnąć bez nich zwykłymi typami induktywnymi
    i będzie to dużo bardziej czytelne oraz prostsze w implementacji. Ba!
    W-typy są nawet nieco słabsze, gdyż go udowodnienia reguły indukcji
    wymagają aksjomatu ekstensjonalności dla funkcji.

    Jednak z tego samego powodu są bardzo ciekawe pod względem teoretycznym -
    wszystko, co można zrobić za pomocą parametryzowanych typów induktywnych,
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

    W kolejnym kroku łączymy argumenty za pomocą produktu:
    niech [A := A1 * ... * Ak]. Wtedy typ [c] wygląda tak:
    [c : A -> T * ... * T -> T]. Zauważmy, że [T * ... * T] możemy zapisać
    równoważnie jako [B -> T], gdzie [B] to typ mający tyle elementów, ile
    razy [T] występuje w produkcie [T * ... * T]. Zatem typ [c] przedstawia
    się tak: [c : A -> (B -> T) -> T].

    Teraz poczynimy kilka uogólnień. Po pierwsze, na początku założyliśmy,
    że [c] ma skończenie wiele argumentów indukcyjnych, ale postać [B -> T]
    uwzględnia także przypadek, gdy jest ich nieskończenie wiele (tzn. gdy
    [c] miał oryginalnie jakiś argument postaci [Y -> T] dla nieskończonego
    [Y]).

    Po drugie, założyliśmy, że [c] jest funkcją niezależną. Przypadek, gdy
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

    Stosując powyższe przekształcenia możemy sprowadzić każdy typ induktywny
    do równoważnej postaci z jednym konstruktorem o typie
    [forall x : A, B x -> T]. Skoro tak, to definiujemy nowy typ, w którym
    [A] i [B] są parametrami... i bum, tak właśnie powstało [W]!

    Podejrzewam, że powyższy opis przyprawia cię o niemały ból głowy. Rzućmy
    więc okiem na przykład, który powinien być wystarczająco ogólny, żeby
    wszystko stało się jasne. *)

Print list.
(* ===> Inductive list (X : Type) : Type :=
            | nil : list X
            | cons : X -> list X -> list X *)

(** Spróbujmy zastosować powyższe przekształcenia na typie [list X], żeby
    otrzymać reprezentację [list] za pomocą [W].

    Zajmijmy się najpierw konstruktorem [nil]. Nie ma on ani argumentów
    indukcyjnych, ani nieindukcyjnych, co zdaje się nie pasować do naszej
    ogólnej metody. Jest to jednak jedynie złudzenie: brak argumentów
    nieindukcyjnych możemy zareprezentować za pomocą argumenu o typie
    [unit], zaś brak argumentów indukcyjnych możemy zareprezentować
    argumentem o typie [False -> list X]. Wobec tego typ konstruktora
    [nil] możemy zapisać jako [unit -> (False -> list X) -> list X].

    Dla [cons]a jest już prościej: argument nieindukcyjny to po prostu [X],
    zaś jeden argument indukcyjny możemy przedstawić jako [unit -> list X].
    Nowy typ [cons]a możemy zapisać jako [X -> (unit -> list X) -> list X].

    Pozostaje nam skleić obydwa konstruktory w jeden. Niech [A := unit + X]
    i niech [B (inl tt) := False, B (inr x) := unit]. W ten sposób dostajemy
    poniższe kodowanie [list] za pomocą [W] (oczywiście nie jest to jedyne
    możliwe kodowanie - równie dobrze zamiast [unit + X] moglibyśmy użyć
    typu [option X]). *)

Module listW.

Definition listW (X : Type) : Type :=
  W (unit + X) (
    fun ux : unit + X =>
    match ux with
        | inl _ => False
        | inr _ => unit
    end).

(** Wartą zauważenia różnicą konceptualną jest to, że jeżeli myślimy
    Coqowymi typami induktywnymi, to [list] ma dwa konstruktory - [nil]
    i [cons], ale gdy myślimy za pomocą [W], to sprawa ma się inaczej.
    Formalnie [listW] ma jeden konstruktor [sup], ale w praktyce jest
    aż [1 + |X|] konstruktorów, gdzie [|X|] oznacza liczbę elementów
    typu [X]. Jeden z nich opdowiada [nil], a każdy z pozostałych [|X|]
    konstruktorów odpowiada [cons x] dla pewnego [x : X]. Jedyną
    pozostałością po oryginalnej liczbie konstruktorów jest liczba
    składników, które pojawiają się w sumie [unit + X].

    Oczywiście posługiwanie się [nil] i [cons] jest dużo wygodniejsze niż
    używanie [sup], więc czas odzyskać utracone konstruktory! *)

Definition nilW (X : Type) : listW X :=
  sup (inl tt) (fun e : False => match e with end).

Definition consW {X : Type} (h : X) (t : listW X) : listW X :=
  sup (inr h) (fun _ : unit => t).

(** Zauważ, że [consW] jest jedynie jednym z wielu możliwych kodowań
    konstruktora [cons]. Inaczej możemy go zakodować np. tak: *)

Definition consW' {X : Type} (h : X) (t : listW X) : listW X :=
  sup (inr h) (fun u : unit => match u with | tt => t end).

(** Kodowania te nie są konwertowalne, ale jeżeli użyjemy aksjomatu
    ekstensjonalności dla funkcji, to możemy pokazać, że są równe. *)

Fail Check eq_refl : consW = consW'.
(* ===> The command has indeed failed with message:
        The term "eq_refl" has type "consW = consW"
        while it is expected to have type "consW = consW'". *)

Require Import FunctionalExtensionality.

Lemma consW_consW' :
  forall {X : Type} (h : X) (t : listW X),
    consW h t = consW' h t.
Proof.
  intros. unfold consW, consW'. f_equal.
  extensionality u. destruct u.
  reflexivity.
Qed.

(** Podobnym mykiem musim posłużyć się, gdy chcemy udowodnić regułę indukcji.
    Dowód zaczynamy od indukcji po [l] (musimy pamiętać, że nasze [W] jest
    typem induktywnym, więc ma regułę indukcji), ale nie możemy bezpośrednio
    użyć hipotez [PnilW] ani [PconsW], gdyż dotyczą one innych kodowań [nil]
    i [cons] niż te, które pojawiają się w celu. Żeby uporać się z problemem,
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

Check W_ind.

Lemma listW_ind' :
  forall
    (X : Type) (P : listW X -> Type)
    (PnilW : P (nilW X))
    (PconsW : forall (h : X) (t : listW X), P t -> P (consW h t)),
      {f : forall l : listW X, P l |
        f (nilW X) = PnilW /\
        forall (h : X) (t : listW X), f (consW h t) = PconsW h t (f t)}.
Proof.
  esplit. Unshelve. Focus 2.
    induction l as [[[] | x] b IH].
      Print nilW.
      replace (P (sup (inl tt) b)) with (P (nilW X)).
        assumption.
        unfold nilW. do 2 f_equal. extensionality e. destruct e.
      replace _ with (P (consW x (b tt))).
        apply PconsW. apply IH.
        unfold consW. do 2 f_equal.
          extensionality u. destruct u. reflexivity.
    cbn. split.
      compute.
Admitted.

(** Skoro mamy regułę indukcji, to bez problemu jesteśmy w stanie pokazać,
    że typy [list X] oraz [listW X] są izomorficzne, tzn. istnieją funkcje
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

(* begin hide *)

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
    unfold zeroW. f_equal. admit.
    rewrite H. unfold succW. f_equal. admit.
Admitted.
(* end hide *)

End listW.

(* end hide *)

(** * M-typy (TODO) *)

(** M-typy to to samo co W-typy, tylko że dualne. Pozdro dla kumatych. *)

(** * Kodowanie Churcha (TODO) *)

(** Achtung: póki co wisi tu kod roboczy *)

(* begin hide *)
Require Import X3.
(* end hide *)

Definition clist (A : Type) : Type :=
  forall X : Type, X -> (A -> X -> X) -> X.

Definition cnil {A : Type} : clist A :=
  fun X nil cons => nil.

Definition ccons {A : Type} : A -> clist A -> clist A :=
  fun h t => fun X nil cons => cons h (t X nil cons).

Notation "c[]" := cnil.
Notation "x :c: y" := (ccons x y) (at level 60, right associativity).
Notation "c[ x ; .. ; y ]" := (ccons x .. (ccons y cnil) ..).

Definition head {A : Type} (l : clist A) : option A :=
  l (option A) None (fun h _ => Some h).

(*
Definition tail {A : Type} (l : clist A) : option (clist A) :=
  l _ None
    (fun h t => t).

Compute tail c[1; 2; 3].
*)

Definition null {A : Type} (l : clist A) : bool :=
  l _ true (fun _ _ => false).

Definition clen {A : Type} (l : clist A) : nat :=
  l nat 0 (fun _ => S).

Definition snoc {A : Type} (l : clist A) (x : A) : clist A :=
  fun X nil cons => l _ (c[x] _ nil cons) cons.

Definition rev {A : Type} (l : clist A) : clist A.
Proof.
  unfold clist in *.
  intros X nil cons.
Abort.

Definition capp {A : Type} (l1 l2 : clist A) : clist A :=
  fun X nil cons => l1 X (l2 X nil cons) cons.

Fixpoint fromList {A : Type} (l : list A) : clist A :=
match l with
    | [] => cnil
    | h :: t => ccons h (fromList t)
end.

Definition toList {A : Type} (l : clist A) : list A :=
  l (list A) [] (@cons A).

Lemma toList_fromList :
  forall (A : Type) (l : list A),
    toList (fromList l) = l.
Proof.
  induction l as [| h t]; compute in *; rewrite ?IHt; reflexivity.
Qed.

Lemma fromList_toList :
  forall (A : Type) (cl : clist A),
    fromList (toList cl) = cl.
Proof.
  intros. unfold clist in *. compute.
Abort.

Definition wut : Type :=
  forall X : Type, (X -> X) -> X.