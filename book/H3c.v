(** * H3c: Relacje a funkcje [TODO] *)

Require Import FunctionalExtensionality Nat Lia.

Require Import List.
Import ListNotations.

From Typonomikon Require Export H3b.

(** * Rodzaje relacji heterogenicznych *)

(** ** Relacje lewo- i prawostronnie unikalne *)

(* begin hide *)
(* TODO: napisać, że lepszą nazwą dla [RightUnique] jest "relacja deterministyczna". *)
(* end hide *)

Class LeftUnique {A B : Type} (R : hrel A B) : Prop :=
{
  left_unique :
    forall (a a' : A) (b : B), R a b -> R a' b -> a = a'
}.

Class RightUnique {A B : Type} (R : hrel A B) : Prop :=
{
  right_unique :
    forall (a : A) (b b' : B), R a b -> R a b' -> b = b'
}.

(** Dwoma podstawowymi rodzajami relacji są relacje unikalne z lewej i prawej
    strony. Relacja lewostronnie unikalna to taka, dla której każde [b : B]
    jest w relacji z co najwyżej jednym [a : A]. Analogicznie definiujemy
    relację prawostronnie unikalną. *)

#[export]
Instance LeftUnique_eq (A : Type) : LeftUnique (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance RightUnique_eq (A : Type) : RightUnique (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Najbardziej elementarną intuicję stojącą za tymi koncepcjami można
    przedstawić na przykładzie relacji równości: jeżeli dwa obiekty są
    równe jakiemuś trzeciemu obiektowi, to muszą być także równe sobie
    nawzajem.

    Pojęcie to jest jednak bardziej ogólne i dotyczy także relacji, które
    nie są homogeniczne. W szczególności jest ono różne od pojęcia relacji
    przechodniej, które pojawi się już niedługo. *)

#[export]
Instance LeftUnique_Rcomp :
  forall (A B C : Type) (R : hrel A B) (S : hrel B C),
    LeftUnique R -> LeftUnique S -> LeftUnique (Rcomp R S).
(* begin hide *)
Proof.
  rel. specialize (left_unique0 _ _ _ H0 H2). subst.
  apply left_unique1 with x0; assumption.
Qed.
(* end hide *)

#[export]
Instance RightUnique_Rcomp :
  forall (A B C : Type) (R : hrel A B) (S : hrel B C),
    RightUnique R -> RightUnique S -> RightUnique (Rcomp R S).
(* begin hide *)
Proof.
  rel. specialize (right_unique1 _ _ _ H H1). subst.
  apply right_unique0 with x0; assumption.
Qed.
(* end hide *)

(** Składanie zachowuje oba rodzaje relacji unikalnych. Nie ma tu co
    za dużo filozofować — żeby się przekonać, narysuj obrazek. TODO. *)

#[export]
Instance LeftUnique_Rinv :
  forall (A B : Type) (R : hrel A B),
    RightUnique R -> LeftUnique (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance RightUnique_Rinv :
  forall (A B : Type) (R : hrel A B),
    LeftUnique R -> RightUnique (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Już na pierwszy rzut oka widać, że pojęcia te są w pewien sposób
    symetryczne. Aby uchwycić tę symetrię, możemy posłużyć się operacją
    [Rinv]. Okazuje się, że zamiana miejscami argumentów relacji lewostronnie
    unikalnej daje relację prawostronnie unikalną i vice versa. *)

#[export]
Instance LeftUnique_Rand :
  forall (A B : Type) (R S : hrel A B),
    LeftUnique R -> LeftUnique (Rand R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance RightUnique_Rand :
  forall (A B : Type) (R S : hrel A B),
    RightUnique R -> RightUnique (Rand R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_LeftUnique_Ror :
  exists (A B : Type) (R S : hrel A B),
    LeftUnique R /\ LeftUnique S /\ ~ LeftUnique (Ror R S).
(* begin hide *)
Proof.
  exists bool, bool, (@eq bool), (fun b b' => b = negb b').
  rel. specialize (left_unique0 true false true).
  contradict left_unique0. intuition.
Qed.
(* end hide *)

Lemma not_RightUnique_Ror :
  exists (A B : Type) (R S : hrel A B),
    RightUnique R /\ RightUnique S /\ ~ RightUnique (Ror R S).
(* begin hide *)
Proof.
  exists bool, bool, (fun b b' => b = negb b'), (@eq bool).
  rel.
  - destruct b, b'; intuition.
  - specialize (right_unique0 true false true).
    contradict right_unique0. intuition.
Qed.
(* end hide *)

(** Koniunkcja relacji unikalnej z inną daje relację unikalną, ale dysjunkcja
    nawet dwóch relacji unikalnych nie musi dawać w wyniku relacji unikalnej.
    Wynika to z interpretacji operacji na relacjach jako operacji na
    kolekcjach par.

    Wyobraźmy sobie, że relacja [R : hrel A B] to kolekcja par [p : A * B].
    Jeżeli para jest elementem kolekcji, to jej pierwszy komponent jest w
    relacji [R] z jej drugim komponentem. Dysjunkcję relacji [R] i [S] w
    takim układzie stanowi kolekcja, która zawiera zarówno pary z kolekcji
    odpowiadającej [R], jak i te z kolekcji odpowiadającej [S]. Koniunkcja
    odpowiada kolekcji par, które są zarówno w kolekcji odpowiadającej [R],
    jak i tej odpowiadającej [S].

    Tak więc dysjunkcja [R] i [S] może do [R] "dorzucić" jakieś pary, ale
    nie może ich zabrać. Analogicznie, koniunkcja [R] i [S] może zabrać
    pary z [R], ale nie może ich dodać.

    Teraz interpretacja naszego wyniku jest prosta. W przypadku relacji
    lewostronnie unikalnych jeżeli każde [b : B] jest w relacji z co
    najwyżej jednym [a : A], to potencjalne zabranie jakichś par z tej
    relacji niczego nie zmieni. Z drugiej strony, nawet jeżeli obie relacje
    są lewostronnie unikalne, to dodanie do [R] par z [S] może spowodować
    wystąpienie powtórzeń, co niszczy unikalność. *)

Lemma not_LeftUnique_Rnot :
  exists (A B : Type) (R : hrel A B),
    LeftUnique R /\ ~ LeftUnique (Rnot R).
(* begin hide *)
Proof.
  pose (R := @eq (option bool)).
  exists (option bool), (option bool), R.
  rel. cut (Some true = Some false).
    inversion 1.
    apply left_unique0 with None; inversion 1.
Qed.
(* end hide *)

Lemma not_RightUnique_Rnot :
  exists (A B : Type) (R : hrel A B),
    LeftUnique R /\ ~ LeftUnique (Rnot R).
(* begin hide *)
Proof.
  pose (R := @eq (option bool)).
  exists (option bool), (option bool), R.
  rel. cut (Some true = Some false).
    inversion 1.
    apply left_unique0 with None; inversion 1.
Qed.
(* end hide *)

(** Negacja relacji unikalnej również nie musi być unikalna. Spróbuj podać
    interpretację tego wyniku z punktu widzenia operacji na kolekcjach par. *)

(** **** Ćwiczenie *)

(** Znajdź przykład relacji, która:
    - nie jest unikalna ani lewostronnie, ani prawostronnie
    - jest unikalna lewostronnie, ale nie prawostronnie
    - jest unikalna prawostronnie, ale nie nie lewostronnie
    - jest obustronnie unikalna *)

(* begin hide *)
Definition Rnegb (b b' : bool) : Prop := b = negb b'.

Definition NRL (b b' : bool) : Prop :=
  if b then b = negb b' else False.

Lemma not_LeftUnique_RTrue_bool :
  ~ LeftUnique (@RTrue bool bool).
Proof.
  compute. destruct 1. cut (true = false).
  - inversion 1.
  - rel.
Qed.

Lemma not_RightUnique_RTrue_bool :
  ~ RightUnique (@RTrue bool bool).
Proof.
  compute. destruct 1. cut (true = false).
  - inversion 1.
  - rel.
Qed.

Definition is_zero (b : bool) (n : nat) : Prop :=
match n with
| 0 => b = true
| _ => b = false
end.

#[export]
Instance LeftUnique_is_zero : LeftUnique is_zero.
Proof.
  split. intros. destruct b; cbn in *; subst; trivial.
Qed.

Lemma not_RightUnique_is_zero : ~ RightUnique is_zero.
Proof.
  destruct 1. cut (1 = 2).
    inversion 1.
    apply right_unique0 with false; cbn; trivial.
Qed.

Definition is_zero' : nat -> bool -> Prop := Rinv is_zero.

Lemma not_LeftUnique_is_zero' : ~ LeftUnique is_zero'.
Proof.
  destruct 1. cut (1 = 2).
    inversion 1.
    apply left_unique0 with false; cbn; trivial.
Qed.

#[export]
Instance RightUnique_is_zero' : RightUnique is_zero'.
Proof.
  split. destruct a; cbn; intros; subst; trivial.
Qed.

#[export]
Instance LeftUnique_RFalse :
  forall A B : Type, LeftUnique (@RFalse A B).
Proof. rel. Qed.

#[export]
Instance RightUnique_RFalse :
  forall A B : Type, RightUnique (@RFalse A B).
Proof. rel. Qed.
(* end hide *)

(** ** Relacje lewo- i prawostronnie totalne *)

Class LeftTotal {A B : Type} (R : hrel A B) : Prop :=
{
  left_total : forall a : A, exists b : B, R a b
}.

Class RightTotal {A B : Type} (R : hrel A B) : Prop :=
{
  right_total : forall b : B, exists a : A, R a b
}.

(** Kolejnymi dwoma rodzajami heterogenicznych relacji binarnych są relacje
    lewo- i prawostronnie totalne. Relacja lewostronnie totalna to taka, że
    każde [a : A] jest w relacji z jakimś elementem [B]. Definicja relacji
    prawostronnie totalnej jest analogiczna.

    Za pojęciem tym nie stoją jakieś wielkie intuicje: relacja lewostronnie
    totalna to po prostu taka, w której żaden element [a : A] nie jest
    "osamotniony". *)

#[export]
Instance LeftTotal_RTrue :
  forall A : Type, LeftTotal (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance RightTotal_RTrue :
  forall A : Type, RightTotal (@RTrue A A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** TODO *)

#[export]
Instance LeftTotal_RFalse_Empty :
  LeftTotal (@RFalse Empty_set Empty_set).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance RightTotal_RFalse_Empty :
  RightTotal (@RFalse Empty_set Empty_set).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_LeftTotal_RFalse_inhabited :
  forall A B : Type,
    A -> ~ LeftTotal (@RFalse A B).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_RightTotal_RFalse_inhabited :
  forall A B : Type,
    B -> ~ RightTotal (@RFalse A B).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** TODO *)

#[export]
Instance LeftTotal_eq :
  forall A : Type, LeftTotal (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance RightTotal_eq :
  forall A : Type, RightTotal (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Równość jest relacją totalną, gdyż każdy term [x : A] jest równy samemu
    sobie. *)

#[export]
Instance LeftTotal_Rcomp :
  forall (A B C : Type) (R : hrel A B) (S : hrel B C),
    LeftTotal R -> LeftTotal S -> LeftTotal (Rcomp R S).
(* begin hide *)
Proof.
  intros A B C R S [LTR] [LTS].
  split; compute; intros a.
  destruct (LTR a) as [b r],
           (LTS b) as [c s].
  exists c, b. split; assumption.
Qed.
(* end hide *)

#[export]
Instance RightTotal_Rcomp :
  forall (A B C : Type) (R : hrel A B) (S : hrel B C),
    RightTotal R -> RightTotal S -> RightTotal (Rcomp R S).
(* begin hide *)
Proof.
  rel. rename b into c.
  destruct (right_total0 c) as [b H].
  destruct (right_total1 b) as [a H'].
  exists a, b. split; assumption.
Qed.
(* end hide *)

#[export]
Instance RightTotal_Rinv :
  forall (A B : Type) (R : hrel A B),
    LeftTotal R -> RightTotal (Rinv R).
(* begin hide *)
Proof.
  unfold Rinv; split. intro a. destruct H.
  destruct (left_total0 a) as [b H]. exists b. assumption.
Qed.
(* end hide *)

#[export]
Instance LeftTotal_Rinv :
  forall (A B : Type) (R : hrel A B),
    RightTotal R -> LeftTotal (Rinv R).
(* begin hide *)
Proof.
  unfold Rinv; split. intro a. destruct H.
  destruct (right_total0 a) as [b H]. exists b. assumption.
Qed.
(* end hide *)

(** Między lewo- i prawostronną totalnością występuje podobna symetria jak
    między dwoma formami unikalności: relacja odwrotna do lewostronnie
    totalnej jest prawostronnie totalna i vice versa. Totalność jest również
    zachowywana przez składanie. *)

Lemma not_LeftTotal_Rnot :
  exists (A B : Type) (R : hrel A B),
    RightTotal R /\ ~ RightTotal (Rnot R).
(* begin hide *)
Proof.
  exists unit, unit, (@eq unit). rel.
  destruct (right_total0 tt), x. apply H. trivial.
Qed.
(* end hide *)

Lemma not_RightTotal_Rnot :
  exists (A B : Type) (R : hrel A B),
    RightTotal R /\ ~ RightTotal (Rnot R).
(* begin hide *)
Proof.
  exists unit, unit, (@eq unit). rel.
  destruct (right_total0 tt), x. apply H. trivial.
Qed.
(* end hide *)

(** Negacja relacji totalnej nie może być totalna. Nie ma się co dziwić —
    negacja wyrzuca z relacji wszystkie pary, których w niej nie było, a
    więc pozbywa się czynnika odpowiedzialnego za totalność. *)

Lemma not_LeftTotal_Rand :
  exists (A B : Type) (R S : hrel A B),
    LeftTotal R /\ LeftTotal S /\ ~ LeftTotal (Rand R S).
(* begin hide *)
Proof.
  exists bool, bool.
  exists (@Rid bool), (fun b b' => b = negb b').
  rel.
    exists (negb a). destruct a; trivial.
    destruct (left_total0 true).
      destruct x, H; cbn in H0; try congruence.
Qed.
(* end hide *)

Lemma not_RightTotal_Rand :
  exists (A B : Type) (R S : hrel A B),
    RightTotal R /\ RightTotal S /\ ~ RightTotal (Rand R S).
(* begin hide *)
Proof.
  exists bool, bool.
  exists (@Rid bool), (fun b b' => b = negb b').
  rel. destruct (right_total0 true).
  destruct x, H; cbn in H0; try congruence.
Qed.
(* end hide *)

Lemma LeftTotal_Ror :
  forall (A B : Type) (R S : hrel A B),
    LeftTotal R -> LeftTotal (Ror R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma RightTotal_Ror :
  forall (A B : Type) (R S : hrel A B),
    RightTotal R -> RightTotal (Ror R S).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Związki totalności z koniunkcją i dysjunkcją relacji są podobne jak
    w przypadku unikalności, lecz tym razem to dysjunkcja zachowuje
    właściwość, a koniunkcja ją niszczy. Wynika to z tego, że dysjunkcja
    nie zabiera żadnych par z relacji, więc nie może uszkodzić totalności.
    Z drugiej strony koniunkcja może zabrać jakąś parę, a wtedy relacja
    przestaje być totalna. *)

(** **** Ćwiczenie *)

(** Znajdź przykład relacji, która:
    - nie jest totalna ani lewostronnie, ani prawostronnie
    - jest totalna lewostronnie, ale nie prawostronnie
    - jest totalna prawostronnie, ale nie nie lewostronnie
    - jest obustronnie totalna *)

(** Bonusowe punkty za relację, która jest "naturalna", tzn. nie została
    wymyślona na chama specjalnie na potrzeby zadania. *)

(* begin hide *)
Lemma not_LeftTotal_RFalse_inhabited' :
  forall A B : Type, A -> ~ LeftTotal (@RFalse A B).
Proof. rel. Qed.

Lemma not_RightTotal_RFalse_inhabited' :
  forall A B : Type, B -> ~ RightTotal (@RFalse A B).
Proof. rel. Qed.

#[export]
Instance LeftTotal_lt : LeftTotal lt.
Proof.
  split. intro. exists (S a). unfold lt. apply le_n.
Qed.

Lemma not_RightTotal_lt : ~ RightTotal lt.
Proof.
  destruct 1. destruct (right_total0 0). inversion H.
Qed.

Lemma not_LeftTotal_gt : ~ LeftTotal gt.
Proof.
  destruct 1. destruct (left_total0 0). inversion H.
Qed.

#[export]
Instance RightTotal_gt : RightTotal gt.
Proof.
  split. intro. exists (S b). unfold gt, lt. trivial.
Qed.

#[export]
Instance LeftTotal_RTrue_inhabited :
  forall A B : Type, B -> LeftTotal (@RTrue A B).
Proof. rel. Qed.

#[export]
Instance RightTotal_RTrue_inhabited :
  forall A B : Type, A -> RightTotal (@RTrue A B).
Proof. rel. Qed.
(* end hide *)

(** * Rodzaje relacji heterogenicznych v2 *)

(** Poznawszy cztery właściwości, jakie relacje mogą posiadać, rozważymy
    teraz relacje, które posiadają dwie lub więcej z tych właściwości. *)

(** ** Relacje funkcyjne *)

Class Functional {A B : Type} (R : hrel A B) : Prop :=
{
  F_LT :> LeftTotal R;
  F_RU :> RightUnique R;
}.

(** Lewostronną totalność i prawostronną unikalność możemy połączyć, by
    uzyskać pojęcie relacji funkcyjnej. Relacja funkcyjna to relacja,
    która ma właściwości takie, jak funkcje — każdy lewostronny argument
    [a : A] jest w relacji z dokładnie jednym [b : B] po prawej stronie. *)

#[export]
Instance fun_to_Functional {A B : Type} (f : A -> B)
  : Functional (fun (a : A) (b : B) => f a = b).
(* begin hide *)
Proof.
  repeat split; intros.
  - exists (f a). trivial.
  - subst. trivial.
Qed.
(* end hide *)

Require Import IndefiniteDescription.

Definition Functional_to_fun
  {A B : Type} (R : hrel A B) (F : Functional R) : A -> B.
Proof.
  intro a. destruct F as [[LT] [RU]].
  specialize (LT a).
  apply constructive_indefinite_description in LT.
  destruct LT as [b _]. exact b.
Qed.

(** Z każdej funkcji można w prosty sposób zrobić relację funkcyjną, ale
    bez dodatkowych aksjomatów nie jesteśmy w stanie z relacji funkcyjnej
    zrobić funkcji. Przemilczając kwestie aksjomatów możemy powiedzieć
    więc, że relacje funkcyjne odpowiadają funkcjom. *)

#[export]
Instance Functional_eq :
  forall A : Type, Functional (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

(** Równość jest rzecz jasna relacją funkcyjną. Funkcją odpowiadającą
    relacji [@eq A] jest funkcja identycznościowa [@id A]. *)

#[export]
Instance Functional_Rcomp :
  forall (A B C : Type) (R : hrel A B) (S : hrel B C),
    Functional R -> Functional S -> Functional (Rcomp R S).
(* begin hide *)
Proof.
  destruct 1, 1; split.
    apply LeftTotal_Rcomp; assumption.
    apply RightUnique_Rcomp; assumption.
Qed.
(* end hide *)

(** Złożenie relacji funkcyjnych również jest relacją funkcyjną. Nie powinno
    nas to dziwić — wszakże relacje funkcyjne odpowiadają funkcjom, a złożenie
    funkcji jest przecież funkcją. Jeżeli lepiej mu się przyjrzeć, to okazuje
    się, że składanie funkcji odpowiada składaniu relacji, a stąd już prosta
    droga do wniosku, że złożenie relacji funkcyjnych jest relacją funkcyjną.
*)

Lemma not_Functional_Rinv :
  exists (A B : Type) (R : hrel A B),
    Functional R /\ ~ Functional (Rinv R).
(* begin hide *)
Proof.
  exists bool, bool, (fun b b' => b' = true).
  split.
  - rel.
  - destruct 1. destruct F_LT0. destruct (left_total0 false) as [b H].
    destruct b; inversion H.
Qed.
(* end hide *)

(** Odwrotność relacji funkcyjnej nie musi być funkcyjna. Dobrą wizualicją
    tego faktu może być np. funkcja f(x) = x^2 na liczbach rzeczywistych.
    Z pewnością jest to funkcja, a zatem relacja funkcyjna. Widać to na jej
    wykresie — każdemu punktowi dziedziny odpowiada dokładnie jeden punkt
    przeciwdziedziny. Jednak po wykonaniu operacji [Rinv], której odpowiada
    tutaj obrócenie układu współrzędnych o 90 stopni, nie otrzymujemy wcale
    wykresu funkcji. Wprost przeciwnie — niektórym punktom z osi X na takim
    wykresie odpowiadają dwa punkty na osi Y (np. punktowi 4 odpowiadają 2
    i -2). Stąd wnioskujemy, że odwrócenie relacji funkcyjnej f nie daje w
    wyniku relacji funkcyjnej. *)

Lemma not_Functional_Rand :
  exists (A B : Type) (R S : hrel A B),
    Functional R /\ Functional S /\ ~ Functional (Rand R S).
(* begin hide *)
Proof.
  exists bool, bool.
  exists (@Rid bool), (fun b b' => b = negb b').
  rel.
    exists (negb a). destruct a; trivial.
    destruct b, b'; cbn in H0; congruence.
    destruct (left_total0 true), x, H; cbn in H0; congruence.
Qed.
(* end hide *)

Lemma not_Functional_Ror :
  exists (A B : Type) (R S : hrel A B),
    Functional R /\ Functional S /\ ~ Functional (Ror R S).
(* begin hide *)
Proof.
  exists bool, bool.
  exists (@Rid bool), (fun b b' => b = negb b').
  rel.
    exists (negb a). destruct a; trivial.
    destruct b, b'; cbn in H0; congruence.
    cut (false = true).
      inversion 1.
      apply right_unique0 with false; auto.
Qed.
(* end hide *)

Lemma not_Functional_Rnot :
  exists (A B : Type) (R : hrel A B),
    Functional R /\ ~ Functional (Rnot R).
(* begin hide *)
Proof.
  pose (A := option bool).
  exists A, A, (@eq A). rel.
  cut (Some true = Some false).
    inversion 1.
    apply right_unique0 with None; inversion 1.
Qed.
(* end hide *)

(** Ani koniunkcje, ani dysjunkcje, ani negacje relacji funkcyjnych nie
    muszą być wcale relacjami funkcyjnymi. Jest to po części konsekwencją
    właściwości relacji lewostronnie totalnych i prawostronnie unikalnych:
    pierwsze mają problem z [Rand], a drugie z [Ror], oba zaś z [Rnot]. *)

(** **** Ćwiczenie *)

(** Możesz zadawać sobie pytanie: po co nam w ogóle pojęcie relacji
    funkcyjnej, skoro mamy funkcje? Funkcje muszą być obliczalne (ang.
    computable) i to na mocy definicji, zaś relacje — niekonieczne.
    Czasem prościej może być najpierw zdefiniować relację, a dopiero
    później pokazać, że jest funkcyjna. Czasem zdefiniowanie danego
    bytu jako funkcji może być niemożliwe.

    Funkcję Collatza klasycznie definiuje się w ten sposób: jeżeli n
    jest parzyste, to f(n) = n/2. W przeciwnym przypadku f(n) = 3n + 1.

    Zaimplementuj tę funkcję w Coqu. Spróbuj zaimplementować ją zarówno
    jako funkcję rekurencyjną, jak i relację. Czy twoja funkcja dokładnie
    odpowiada powyższej specyfikacji? Czy jesteś w stanie pokazać, że twoja
    relacja jest funkcyjna?

    Udowodnij, że f(42) = 1. *)

(* begin hide *)
Fixpoint collatz' (fuel n : nat) : list nat :=
match fuel with
| 0 => []
| S fuel' =>
  if leb n 1 then [n] else
      let h := if even n then div2 n else 1 + 3 * n
      in n :: collatz' fuel' h
end.

(*
Compute map (collatz' 1000) [1; 2; 3; 4; 5; 6; 7; 8; 9].
Compute collatz' 1000 2487.
*)

Inductive collatz : nat -> nat -> Prop :=
| c_even : forall n : nat, collatz (2 * n) n
| c_odd : forall n : nat, collatz (1 + 2 * n) (4 + 6 * n)
| c_trans :
    forall a b c : nat,
      collatz a b -> collatz b c -> collatz a c.

#[global] Hint Constructors collatz : core.

Lemma collatz_42 : collatz 42 1.
Proof.
  apply c_trans with 21.
    change 42 with (2 * 21). constructor.
  apply c_trans with 64.
    change 21 with (1 + 2 * 10). constructor.
  apply c_trans with 2.
    2: apply (c_even 1).
  apply c_trans with 4.
    2: apply (c_even 2).
  apply c_trans with 8.
    2: apply (c_even 4).
  apply c_trans with 16.
    2: apply (c_even 8).
  apply c_trans with 32.
    2: apply (c_even 16).
  apply (c_even 32).
Qed.
(* end hide *)

(** ** Relacje injektywne *)

Class Injective {A B : Type} (R : hrel A B) : Prop :=
{
  I_Fun :> Functional R;
  I_LU :> LeftUnique R;
}.

(* TODO: injective
#[export]
Instance inj_to_Injective :
  forall (A B : Type) (f : A -> B),
    injective f -> Injective (fun (a : A) (b : B) => f a = b).
(* begin hide *)
Proof.
  split.
    apply fun_to_Functional.
    rel.
Qed.
(* end hide *)
*)

(** Relacje funkcyjne, które są lewostronnie unikalne, odpowiadają funkcjom
    injektywnym. *)

#[export]
Instance Injective_eq :
  forall A : Type, Injective (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Injective_Rcomp :
  forall (A B C : Type) (R : hrel A B) (S : hrel B C),
    Injective R -> Injective S -> Injective (Rcomp R S).
(* begin hide *)
Proof.
  split; destruct H, H0.
    apply Functional_Rcomp; assumption.
    apply LeftUnique_Rcomp; assumption.
Qed.
(* end hide *)

Lemma not_Injective_Rinv :
  exists (A B : Type) (R : hrel A B),
    Injective R /\ ~ Injective (Rinv R).
(* begin hide *)
Proof.
  exists bool, (option bool),
  (fun (b : bool) (ob : option bool) => Some b = ob).
  rel.
    destruct (left_total0 None) as [b H]. inversion H.
Qed.
(* end hide *)

Lemma not_Injective_Rand :
  exists (A B : Type) (R S : hrel A B),
    Injective R /\ Injective S /\ ~ Injective (Rand R S).
(* begin hide *)
Proof.
  exists bool, bool.
  exists (@Rid bool), (fun b b' => b = negb b').
  rel.
    exists (negb a). destruct a; trivial.
    destruct b, b'; cbn in H0; congruence.
    destruct (left_total0 true). destruct x, H; cbn in H0; congruence.
Qed.
(* end hide *)

Lemma not_Injective_Ror :
  exists (A B : Type) (R S : hrel A B),
    Injective R /\ Injective S /\ ~ Injective (Ror R S).
(* begin hide *)
Proof.
  exists bool, bool.
  exists (@Rid bool), (fun b b' => b = negb b').
  rel.
    exists (negb a). destruct a; trivial.
    destruct b, b'; cbn in H0; congruence.
    cut (false = true).
      inversion 1.
      apply right_unique0 with false; auto.
Qed.
(* end hide *)

Lemma not_Injective_Rnot :
  exists (A B : Type) (R : hrel A B),
    Injective R /\ ~ Injective (Rnot R).
(* begin hide *)
Proof.
  pose (A := option bool).
  exists A, A, (@eq A).
  rel. cut (Some true = Some false).
    inversion 1.
    apply right_unique0 with None; inversion 1.
Qed.
(* end hide *)

(** Właściwości relacji injektywnych są takie, jak funkcji injektywnych,
    gdyż te pojęcia ściśle sobie odpowiadają. *)

(** **** Ćwiczenie *)

(** Udowodnij, że powyższe zdanie nie kłamie. *)

(* TODO: injective
Lemma injective_Injective :
  forall (A B : Type) (f : A -> B),
    injective f <-> Injective (fun (a : A) (b : B) => f a = b).
(* begin hide *)
Proof.
  split.
    compute; intros. repeat split; intros.
      exists (f a). reflexivity.
      rewrite <- H0, <- H1. reflexivity.
      apply H. rewrite H0, H1. reflexivity.
    destruct 1 as [[[] []] []]. red. intros.
      apply left_unique0 with (f x').
        assumption.
        reflexivity.
Qed.
(* end hide *)
*)

(** ** Relacje surjektywne *)

Class Surjective {A B : Type} (R : hrel A B) : Prop :=
{
  S_Fun :> Functional R;
  S_RT :> RightTotal R;
}.

(* TODO: surjective
#[export]
Instance sur_to_Surjective :
  forall (A B : Type) (f : A -> B),
    surjective f -> Surjective (fun (a : A) (b : B) => f a = b).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)
*)

(** Relacje funkcyjne, które są prawostronnie totalne, odpowiadają funkcjom
    surjektywnym. *)

#[export]
Instance Surjective_eq :
  forall A : Type, Surjective (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Surjective_Rcomp :
  forall (A B C : Type) (R : hrel A B) (S : hrel B C),
    Surjective R -> Surjective S -> Surjective (Rcomp R S).
(* begin hide *)
Proof.
  split; destruct H, H0.
    apply Functional_Rcomp; assumption.
    apply RightTotal_Rcomp; assumption.
Qed.
(* end hide *)

Lemma not_Surjective_Rinv :
  exists (A B : Type) (R : hrel A B),
    Surjective R /\ ~ Surjective (Rinv R).
(* begin hide *)
Proof.
  exists (option bool), bool,
  (fun (ob : option bool) (b : bool) =>
  match ob with
  | None => b = true
  | Some _ => ob = Some b
  end).
  rel.
    destruct a; eauto.
    destruct a, b, b'; congruence.
    exists (Some b). trivial.
    cut (None = Some true).
      inversion 1.
      apply right_unique0 with true; auto.
Qed.
(* end hide *)

Lemma not_Surjective_Rand :
  exists (A B : Type) (R S : hrel A B),
    Surjective R /\ Surjective S /\ ~ Surjective (Rand R S).
(* begin hide *)
Proof.
  exists bool, bool.
  exists (@Rid bool), (fun b b' => b = negb b').
  rel.
    exists (negb a). destruct a; trivial.
    destruct b, b'; cbn in H0; congruence.
    destruct (left_total0 true). destruct x, H; cbn in H0; congruence.
Qed.
(* end hide *)

Lemma not_Surjective_Ror :
  exists (A B : Type) (R S : hrel A B),
    Surjective R /\ Surjective S /\ ~ Surjective (Ror R S).
(* begin hide *)
Proof.
  exists bool, bool.
  exists (@Rid bool), (fun b b' => b = negb b').
  rel.
    exists (negb a). destruct a; trivial.
    destruct b, b'; cbn in H0; congruence.
    cut (false = true).
      inversion 1.
      apply right_unique0 with false; auto.
Qed.
(* end hide *)

Lemma not_Surjective_Rnot :
  exists (A B : Type) (R : hrel A B),
    Surjective R /\ ~ Surjective (Rnot R).
(* begin hide *)
Proof.
  pose (A := option bool).
  exists A, A, (@eq A). rel.
  cut (Some true = Some false).
    inversion 1.
    apply right_unique0 with None; inversion 1.
Qed.
(* end hide *)

(** Właściwości relacji surjektywnych także są podobne do tych, jakie są
    udziałem relacji funkcyjnych. *)

(** ** Relacje bijektywne *)

Class Bijective {A B : Type} (R : hrel A B) : Prop :=
{
  B_Fun :> Functional R;
  B_LU :> LeftUnique R;
  B_RT :> RightTotal R;
}.

(* begin hide *)
(* TODO: bijective
#[export]
Instance bij_to_Bijective :
  forall (A B : Type) (f : A -> B),
    bijective f -> Bijective (fun (a : A) (b : B) => f a = b).
Proof. rel. Qed.
(* end hide *)
*)

(** Relacje funkcyjne, które są lewostronnie totalne (czyli injektywne) oraz
    prawostronnie totalne (czyli surjektywne), odpowiadają bijekcjom. *)

#[export]
Instance Bijective_eq :
  forall A : Type, Bijective (@eq A).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

#[export]
Instance Bijective_Rcomp :
  forall (A B C : Type) (R : hrel A B) (S : hrel B C),
    Bijective R -> Bijective S -> Bijective (Rcomp R S).
(* begin hide *)
Proof.
  split; destruct H, H0.
    apply Functional_Rcomp; assumption.
    apply LeftUnique_Rcomp; assumption.
    apply RightTotal_Rcomp; assumption.
Qed.
(* end hide *)

#[export]
Instance Bijective_Rinv :
  forall (A B : Type) (R : hrel A B),
    Bijective R -> Bijective (Rinv R).
(* begin hide *)
Proof. rel. Qed.
(* end hide *)

Lemma not_Bijective_Rand :
  exists (A B : Type) (R S : hrel A B),
    Bijective R /\ Bijective S /\ ~ Bijective (Rand R S).
(* begin hide *)
Proof.
  exists bool, bool.
  exists (@Rid bool), (fun b b' => b = negb b').
  rel.
    exists (negb a). destruct a; trivial.
    destruct b, b'; cbn in H0; congruence.
    destruct (left_total0 true). destruct x, H; cbn in H0; congruence.
Qed.
(* end hide *)

Lemma not_Bijective_Ror :
  exists (A B : Type) (R S : hrel A B),
    Bijective R /\ Bijective S /\ ~ Bijective (Ror R S).
(* begin hide *)
Proof.
  exists bool, bool.
  exists (@Rid bool), (fun b b' => b = negb b').
  rel.
    exists (negb a). destruct a; trivial.
    destruct b, b'; cbn in H0; congruence.
    cut (false = true).
      inversion 1.
      apply right_unique0 with false; auto.
Qed.
(* end hide *)

Lemma not_Bijective_Rnot :
  exists (A B : Type) (R : hrel A B),
    Bijective R /\ ~ Bijective (Rnot R).
(* begin hide *)
Proof.
  pose (A := option bool).
  exists A, A, (@eq A). rel.
  cut (Some true = Some false).
    inversion 1.
    apply right_unique0 with None; inversion 1.
Qed.
(* end hide *)

(** Właściwości relacji bijektywnych różnią się jednym szalenie istotnym
    detalem od właściwości relacji funkcyjnych, injektywnych i surjektywnych:
    odwrotność relacji bijektywnej jest relacją bijektywną. *)

(** * Nieco więcej o relacjach funkcyjnych (TODO) *)

(** Pojęcie relacji funkcyjnej jest dość zwodnicze, więc pochylimy się nad nim
    nieco dłużej. *)

(** ** Relacje funkcyjne a aksjomat wyboru (TODO) *)

(** Tutaj zademonstrować różnicę między [Functional] a poniższym tworem: *)

Class FunctionalAC {A B : Type} (R : hrel A B) : Prop :=
  fac : exists f : A -> B, forall (a : A) (b : B), R a b <-> f a = b.

(** ** Relacje funkcyjne a funkcje (TODO) *)

(** Tutaj powtórka historyjki z rozdziału o rozstrzygalności. Dowiedzieliśmy
    się tam, że fakt, że zdanie jest określone, nie oznacza jeszcze, że jest
    ono rozstrzygalne. Zdanie jest określone, gdy spełnia zachodzi dla niego
    wyłączony środek, zaś rozstrzygalne, gdy istnieje program, który sprawdza,
    która z tych dwóch możliwości zachodzi. Podobna sytuacja ma miejsce dla
    przeróżnych porządków: to, że relacja jest np. trychotomiczna, nie znaczy
    jeszcze, że potrafimy napisać program, który sprawdza, który z argumentów
    jest większy.

    Z relacjami funkcyjnymi jest podobnie: to, że relacja jest funkcyjna, nie
    znaczy od razu, że potrafimy znaleźć funkcję, której jest ona wykresem. *)

(** ** Relacje wykresowe (TODO) *)

Class Graphic {A B : Type} (R : A -> B -> Prop) : Type :=
{
  grapher : A -> B;
  is_graph : forall (a : A) (b : B), R a b <-> grapher a = b;
}.

(** * Zależności między różnymi rodzajami relacji *)

#[export]
Instance CoReflexive_LeftUnique :
  forall {A : Type} (R : rel A),
    LeftUnique R -> CoReflexive (Rcomp R (Rinv R)).
(* begin hide *)
Proof.
  intros A R [H].
  split; unfold Rinv.
  intros x y (z & r & r').
  eapply H; eassumption.
Qed.
(* end hide *)

Lemma Reflexive_from_Symmetric_Transitive_RightTotal :
  forall {A : Type} (R : rel A),
    Symmetric R -> Transitive R -> RightTotal R -> Reflexive R.
(* begin hide *)
Proof.
  intros A R [HS] [HT] [HRT].
  split; intros x.
  destruct (HRT x) as [y r].
  apply HT with y.
  - apply HS. assumption.
  - assumption.
Qed.
(* end hide *)

#[export]
Instance LeftTotal_Reflexive :
  forall {A : Type} (R : rel A),
    Reflexive R -> LeftTotal R.
(* begin hide *)
Proof.
  intros A R [HR]; split; intros x.
  exists x. apply HR.
Qed.
(* end hide *)

#[export]
Instance RightTotal_Reflexive :
  forall {A : Type} (R : rel A),
    Reflexive R -> RightTotal R.
(* begin hide *)
Proof.
  intros A R [HR]; split; intros x.
  exists x. apply HR.
Qed.
(* end hide *)

#[export]
Instance LeftUnique_CoReflexive :
  forall {A : Type} (R : rel A),
    CoReflexive R -> LeftUnique R.
(* begin hide *)
Proof.
  intros A R [CR]; split; intros x1 x2 y rx1y rx2y.
  rewrite (CR _ _ rx1y), (CR _ _ rx2y). reflexivity.
Qed.
(* end hide *)

#[export]
Instance RightUnique_CoReflexive :
  forall {A : Type} (R : rel A),
    CoReflexive R -> RightUnique R.
(* begin hide *)
Proof.
  intros A R [CR]; split; intros x y1 y2 rxy1 rxy2.
  rewrite <- (CR _ _ rxy1), <- (CR _ _ rxy2). reflexivity.
Qed.
(* end hide *)