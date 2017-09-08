(** Ćwiczenie 10. *)
Theorem ex_and_impl : forall (A : Type) (P Q : A -> Prop),
    (exists x : A, P x /\ Q x) -> (exists y : A, P y) /\ (exists z : A, Q z).
Proof.
  intros. destruct H as [x H]. destruct H.
  split; exists x; assumption.
Restart.
  intros. destruct H as [x [HP HQ]].
  (** Zauważ, że wzorce przekazywane do taktyki 'destruct' można zagnieżdżać,
     dzięki czemu unikamy nadmiernego pisania, gdy nasze hipotezy są
     mocno zagnieżdżone (np. wielokrotna koniunkcja). *)
  split; exists x; assumption.
Restart.
  intros A P Q [x [HP HQ]].
  (** Taktyki 'intros' i 'destruct' można połączyć, przekazując
     jako argumenty dla taktyki 'intro' wzorce zamiast nazw. *)
  split; exists x; assumption.
Qed.



Fixpoint fac (n : nat) : nat :=
match n with
    | 0 => 1
    | S n' => n * fac n'
end.

Require Import Arith.

Theorem le_1_fac : forall n : nat, 1 <= fac n.
Proof.
  induction n as [| n']; simpl.
    auto.
    apply le_plus_trans. assumption.
Qed.

Theorem le_lin_fac : forall n : nat, n <= fac n.
Proof.
  induction n as [| n']; simpl.
    auto.
    replace (S n') with (1 + n'); auto.
    apply plus_le_compat.
      apply le_1_fac.
      replace n' with (n' * 1) at 1.
        apply mult_le_compat_l. apply le_1_fac.
        rewrite mult_comm. simpl. rewrite plus_comm. simpl. trivial.
Qed.

Fixpoint pow2 (n : nat) : nat :=
match n with
    | 0 => 1
    | S n' => 2 * pow2 n'
end.

Theorem le_exp_Fac : forall n : nat,
    4 <= n -> pow2 n <= fac n.
Proof.
  induction 1; simpl.
    repeat constructor.
    rewrite plus_0_r. apply plus_le_compat.
      assumption.
      replace (pow2 m) with (1 * pow2 m).
        apply mult_le_compat.
          apply le_trans with 4; auto.
          assumption.
        rewrite mult_1_l. trivial.
Qed.

(* begin hide *)
(*Fixpoint foldr {A B : Type} (f : A -> B -> B) (l : list A) (b : B)
    : B :=
match l with
  | [] => b
  | h :: t => f h (foldr f t b)
end.

Eval compute in foldr plus [1; 2; 3; 4; 5] 0.*)
(* end hide *)



(** 

    Definicja ta, powszechnie używana, koncentruje się na tym, jak sprawdzić,
    czy dana liczba jest parzysta. Gdy powyższą definicję zmaterializujemy w
    funkcji [p : nat -> bool], będziemy mogli wygenerować wszystkie liczby
    parzyste po prostu generując wszystkie liczby naturalne i odsiewając te,
    dla których [p n = false]. *)

(** Definicja ta różni się znacznie od tej przytoczonej wcześniej. Jest tak,
    gdyż koncentruje się ona na tym, jak wygenerować wszystkie liczby
    parzyste. Gdy potrafimy je generować, możemy także sprawdzać, czy liczba
    jest parzysta, po prostu sprawdzając czy można ją wygenerować.

    Obydwa sposoby definiowania predykatów znacznie się od siebie różnią.
    W definicjach induktywnych możemy używać dowolnych zdań, a zatem
    umożliwiają one zdefiniowanie szerszej klasy obiektów, ale ceną tego
    jest w nierozstrzygalność — sprawdzenie, czy term posiada daną właściwość
    wymaga dowodu, którego w ogólności nie można zautomatyzować. 
    
 *)

(** Wróćmy do zdefiniowanego przez nas uprzednio predykatu [even]. Ponieważ
    został on zdefiniowany induktywnie, każde wystąpienie termu [even n]
    jest zdaniem logicznym, które może posiadać dowód lub nie.

    Zdania logiczne możemy podzielić na rozstrzygalne (ang. decidable)
    i nierozstrzygalne (ang. undecidable). Zdania rozstrzygalne to takie,
    których prawdziwość lub fałszywość można sprawdzić za pomocą jakiejś
    funkcji rekurencyjnej. Zdania nierozstrzygalne nie mają tej właściwości.
    Podział ten rozciąga się również na predykaty, relacje oraz ogólnie
    problemy, które napotykamy.

    
(** Zauważ, że (domyślna) logika, którą posługujemy się w Coqu, jest
    konstruktywna, a więc nie ma w niej prawa wyłączonego środka:
    nie jest tak, że każde zdanie jest prawdziwe lub fałszywe. Tego
    faktu możemy użyć do podania formalnej definicji rozstrzygalności. *)

Dotychczas nauczyliśmy się, że typy możemy definiować induktywnie,
    a funkcje operujące na tych typach — rekurencyjnie. W świecie logiki
    używaliśmy indukcji do definiowania predykatów i relacji. Zadajmy
    sobie teraz pytanie: a co z rekursją? *)

Fixpoint evenb (n : nat) : bool :=
match n with
    | 0 => true
    | 1 => false
    | S (S n') => evenb n'
end.

(** Funkcja [evenb] zwraca [true], gdy jej argument jest parzysty, zaś
    [false], gdy jest nieparzysty. Możemy myśleć o niej jako o odpowiedniku
    zdefiniowanego przez nas wcześniej induktywnego predykatu [even].

    Definicja rekurecyjna różni się od induktywnej już na pierwszy
    rzut oka: pattern matching ma trzy przypadki, podczas gdy w
    definicji induktywnej wystąpiły jedynie dwa konstruktory. Wynika
    to z faktu, że definicja induktywna mówi jedynie, kiedy liczba
    jest parzysta, milczy zaś o liczbach, które parzyste nie są.
    Żeby udowodnić, że liczba nie jest parzysta, musimy posłużyć się
    negacją i udowodnić zdanie [~ even n].
*)

   

(** Definicje induktywne są silniejsze, niż definicje rekurencyjne funkcji,
    których przeciwdziedziną jest typ [bool]. Te pierwsze pozwalają nam
    definiować dowolne relacje oraz predykaty (także te nierozstrzygalne),
    zaś te drugie jedynie funkcje rozstrzygające prawdziwość pewnych zdań —
    zdania te muszą być rozstrzygalne.

    Mimo tych różnic zarówno definicje induktywne jak i rekurencyjne są
    przydatne *)


Time Eval vm_compute in evenb 4.
(* ===> = false : bool
   Finished transaction in 0. secs (0.009998u,0.s) *)

(*Theorem even_dec : forall n : nat, even n \/ ~ even n.
(* begin hide *)
Proof.*)    

Theorem even_n_Sn : forall n : nat,
    even n -> even (S n) -> False.
Proof.
  induction n as [| n'].
    inversion 2.
    intros. apply IHn'.
      inversion H0; subst. assumption.
      assumption.
Qed.
Require Import Arith.

Fixpoint div2 (n : nat) : nat :=
match n with
    | 0 => 0
    | 1 => 1
    | S (S n') => S (div2 n')
end.

Theorem div2_2n : forall n : nat, div2 (2 * n) = n.
Proof.
  induction n as [| n']; simpl in *.
    trivial.
    rewrite <- plus_n_O. induction n'; simpl in *.
      trivial. rewrite plus_comm. simpl in *. do 2 f_equal.
Fixpoint range (n : nat) : list nat :=
match n with
    | 0 => [0]
    | S n' => n :: range n'
end.

Fixpoint rev' {A : Type} (l : list A) : list A :=
    (fix f (l acc : list A) : list A :=
     match l with
         | [] => acc
         | h :: t => f t (h :: acc)
     end) l [].

(*Time Eval compute in rev (range 2500).
Time Eval compute in rev' (range 2000).*)


Lemma rev'_aux : forall (A : Type) (l1 l2 : list A),
    rev' (l1 ++ l2) = rev' l2 ++ rev' l1.
Proof.
  induction l1 as [| h1 t1]; intros.
    simpl. rewrite app_nil_r. trivial.
    simpl. unfold rev' in IHt1.

Theorem rev_rev' : forall (A : Type) (l : list A),
    rev l = rev' l.
(* begin hide *)
Proof.
  induction l as [| h t].
    simpl. trivial.
    change (rev (h :: t)) with (rev t ++ rev [h]). rewrite IHt.
      simpl. simpl.

Theorem rev'_inv : forall (A : Type) (l : list A),
    rev' (rev' l) = l.
(* begin hide *)
Proof.
  induction l as [| h t].
    simpl. trivial.
    simpl. unfold rev' in *.