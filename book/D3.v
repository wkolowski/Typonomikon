(** * D3: Logika boolowska, rozstrzygalność i reflekcja [TODO] *)

(** UWAGA: ten rozdział właśnie ulega konceptualnemu przeobrażeinu i
    może być nie na miejscu, tzn. zawierać rzeczy, o których jeszcze
    nie było mowy. *)

(** * Logika boolowska *)

(** Zadania z funkcji boolowskich, sprawdzające radzenie sobie w pracy
    z enumeracjami, definiowaniem funkcji przez dopasowanie do wzorca
    i dowodzeniem przez rozbicie na przypadki.

    Chciałem, żeby nazwy twierdzeń odpowiadały tym z biblioteki standardowej,
    ale na razie nie mam siły tego ujednolicić. *)

Section boolean_functions.
Variables b b1 b2 b3 : bool.

(** ** Definicje *)

(** Zdefiniuj następujące funkcje boolowskie:
    - [negb] (negacja)
    - [andb] (koniunkcja)
    - [orb] (alternatywa)
    - [implb] (implikacja)
    - [eqb] (równoważność)
    - [xorb] (alternatywa wykluczająca)
    - [nor]
    - [nand] *)

(* begin hide *)
Definition negb (b : bool) : bool :=
match b with
    | true => false
    | false => true
end.

Definition andb (b1 b2 : bool) : bool :=
match b1 with
    | true => b2
    | false => false
end.

Definition orb (b1 b2 : bool) : bool :=
match b1 with
    | true => true
    | false => b2
end.

Definition implb (b1 b2 : bool) : bool :=
match b1 with
    | true => b2
    | false => true
end.

Definition eqb (b1 b2 : bool) : bool :=
match b1, b2 with
    | true, true => true
    | false, false => true
    | _, _ => false
end.

Definition xorb (b1 b2 : bool) : bool :=
match b1, b2 with
    | true, false => true
    | false, true => true
    | _, _ => false
end.

Definition nandb (b1 b2 : bool) : bool := negb (andb b1 b2).
Definition norb (b1 b2 : bool) : bool := negb (orb b1 b2).
(* end hide *)

Notation "b1 && b2" := (andb b1 b2).
Notation "b1 || b2" := (orb b1 b2).

(** ** Twierdzenia *)

(** Udowodnij, że zdefiniowane przez ciebie funkcje mają spodziewane
    właściwości. *)

(* begin hide *)
Ltac solve_bool := intros; match goal with
    | b : bool |- _ => destruct b; clear b; solve_bool
    | _ => cbn; auto
end.
(* end hide *)

(** *** Właściwości negacji *)

Lemma negb_inv : negb (negb b) = b.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Lemma negb_ineq : negb b <> b.
(* begin hide *)
Proof. destruct b; discriminate. Qed.
(* end hide *)

(** *** Eliminacja *)

Lemma andb_elim_l : b1 && b2 = true -> b1 = true.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Lemma andb_elim_r : b1 && b2 = true -> b2 = true.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Lemma andb_elim : b1 && b2 = true -> b1 = true /\ b2 = true.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Lemma orb_elim : b1 || b2 = true -> b1 = true \/ b2 = true.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

(** *** Elementy neutralne *)

Lemma andb_true_neutral_l : true && b = b.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Lemma andb_true_neutral_r : b && true = b.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Lemma orb_false_neutral_l : false || b = b.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Lemma orb_false_neutral_r : b || false = b.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

(** *** Anihilacja *)

Lemma andb_false_annihilation_l : false && b = false.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Lemma andb_false_annihilation_r : b && false = false.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Lemma orb_true_annihilation_l :  true || b = true.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Lemma orb_true_annihilation_r :  b || true = true.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

(** *** Łączność *)

Lemma andb_assoc : b1 && (b2 && b3) = (b1 && b2) && b3.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Lemma orb_assoc : b1 || (b2 || b3) = (b1 || b2) || b3.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

(** *** Przemienność *)

Lemma andb_comm : b1 && b2 = b2 && b1.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Lemma orb_comm : b1 || b2 = b2 || b1.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

(** *** Rozdzielność *)

Lemma andb_dist_orb :
  b1 && (b2 || b3) = (b1 && b2) || (b1 && b3).
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Lemma orb_dist_andb :
  b1 || (b2 && b3) = (b1 || b2) && (b1 || b3).
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

(** *** Wyłączony środek i niesprzeczność *)

Lemma andb_negb : b && negb b = false.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Lemma orb_negb : b || negb b = true.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

(** *** Prawa de Morgana *)

Lemma negb_andb : negb (b1 && b2) = negb b1 || negb b2.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Lemma negb_orb : negb (b1 || b2) = negb b1 && negb b2.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

(** *** [eqb], [xorb], [norb], [nandb] *)

Lemma eqb_spec : eqb b1 b2 = true -> b1 = b2.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Lemma eqb_spec' : eqb b1 b2 = false -> b1 <> b2.
(* begin hide *)
Proof. destruct b1, b2; do 2 inversion 1. Qed.
(* end hide *)

Lemma xorb_spec :
  xorb b1 b2 = negb (eqb b1 b2).
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Lemma xorb_spec' :
  xorb b1 b2 = true -> b1 <> b2.
(* begin hide *)
Proof. destruct b1, b2; do 2 inversion 1. Qed.
(* end hide *)

Lemma norb_spec :
  norb b1 b2 = negb (b1 || b2).
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Lemma nandb_spec :
  nandb b1 b2 = negb (b1 && b2).
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

(** *** Różne *)

Lemma andb_eq_orb :
  b1 && b2 = b1 || b2 -> b1 = b2.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Lemma all3_spec :
  (b1 && b2) || (negb b1 || negb b2) = true.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Lemma noncontradiction_bool :
  negb (eqb b (negb b)) = true.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Lemma excluded_middle_bool :
  b || negb b = true.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

End boolean_functions.

(** * Rozstrzygalność *)

Lemma excluded_middle :
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

Lemma True_dec : True \/ ~ True.
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

Lemma eq_nat_dec :
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
   the return type has sort "Type" while it should be "Prop".
   Elimination of an inductive object of sort Prop
   is not allowed on a predicate in sort Type
   because proofs can be eliminated only to build proofs. *)

(** Nasza porażka wynika z faktu, że do zdefiniowania funkcji, która
    jest programem (jej dziedzina i przeciwdziedzina są sortu [Type])
    próbowaliśmy użyć termu [eq_nat_dec n h], który jest dowodem
    (konkluzją [eq_nat_dec] jest równość, która jest sortu [Prop]).

    Mimo korespondencji Curry'ego-Howarda, która odpowiada za olbrzymie
    podobieństwo specyfikacji i zdań, programów i dowodów, sortu [Type]
    i sortu [Prop], są one rozróżniane i niesie to za sobą konsekwencje:
    podczas gdy programów możemy używać wszędzie, dowodów możemy używać
    jedynie do konstruowania innych dowodów.

    Praktycznie oznacza to, że mimo iż równość liczb naturalnych jest
    rozstrzygalna, pisząc program nie mamy możliwości jej rozstrzygania
    za pomocą [eq_nat_dec]. To właśnie miałem na myśli pisząc, że termy
    typu [P \/ ~ P] są mocno bezużyteczne.

    Uszy do góry: nie wszystko stracone! Jest to tylko drobna przeszkoda,
    którą bardzo łatwo ominąć: *)

Inductive sumbool (A B : Prop) : Type :=
    | left : A -> sumbool A B
    | right : B -> sumbool A B.

(** Typ [sumbool] jest niemal dokładną kopią [or], jednak nie żyje on
    w [Prop], lecz w [Type]. Ta drobna sztuczka, że termy typu
    [sumbool A B] formalnie są programami, mimo że ich naturalna
    interpretacja jest taka sama jak [or], a więc jako dowodu
    dysjunkcji. *)

(** **** Ćwiczenie *)

(** Udowodnij twierdzenie [eq_nat_dec'] o rozstrzygalności [=] na
    liczbach naturalnych. Użyj typu [sumbool]. Następnie napisz
    funkcję [inb_nat], która sprawdza, czy liczba naturalna [n]
    jest obecna na liście [l]. *)

(** ** Kiedy nie warto rozstrzygać? *)

(** Tutaj coś w stylu [n < m \/ n = m \/ n > m] *)

(** ** Rozstrzygalność jako pułapka na negacjonistów *)

Module weak_apart.

Inductive unequal {A : Type} : list A -> list A -> Prop :=
    | nil_cons : forall h t, unequal nil (cons h t)
    | cons_nil : forall h t, unequal (cons h t) nil
    | cons_cons1 :
        forall h1 h2 t1 t2,
          h1 <> h2 -> unequal (cons h1 t1) (cons h2 t2)
    | cons_cons2 :
        forall h1 h2 t1 t2,
          unequal t1 t2 -> unequal (cons h1 t1) (cons h2 t2).

Fixpoint neq {A : Type} (l1 l2 : list A) : Prop :=
match l1, l2 with
    | nil, nil => False
    | nil, cons _ _ => True
    | cons _ _, nil => True
    | cons h1 t1, cons h2 t2 => h1 <> h2 \/ neq t1 t2
end.

Goal
  forall {A : Type} (l1 l2 : list A),
    unequal l1 l2 <-> neq l1 l2.
Proof.
  split.
    induction 1; cbn; firstorder.
    revert l2. induction l1 as [| h1 t1]; destruct l2 as [| h2 t2]; cbn.
      contradiction.
      1-2: constructor.
      destruct 1.
        constructor 3. assumption.
        constructor 4. apply IHt1. assumption.
Qed.

End weak_apart.

Module param_apart.

Inductive unequal
  {A : Type} (apart : A -> A -> Prop) : list A -> list A -> Prop :=
    | nil_cons : forall h t, unequal apart nil (cons h t)
    | cons_nil : forall h t, unequal apart (cons h t) nil
    | cons_cons1 :
        forall h1 h2 t1 t2,
          apart h1 h2 -> unequal apart (cons h1 t1) (cons h2 t2)
    | cons_cons2 :
        forall h1 h2 t1 t2,
          unequal apart t1 t2 -> unequal apart (cons h1 t1) (cons h2 t2).

Fixpoint neq
  {A : Type} (apart : A -> A -> Prop) (l1 l2 : list A) : Prop :=
match l1, l2 with
    | nil, nil => False
    | nil, cons _ _ => True
    | cons _ _, nil => True
    | cons h1 t1, cons h2 t2 => apart h1 h2 \/ neq apart t1 t2
end.

Goal
  forall {A : Type} (apart : A -> A -> Prop) (l1 l2 : list A),
    unequal apart l1 l2 <-> neq apart l1 l2.
Proof.
  split.
    induction 1; cbn; firstorder.
    revert l2. induction l1 as [| h1 t1]; destruct l2 as [| h2 t2]; cbn.
      contradiction.
      1-2: constructor.
      destruct 1.
        constructor 3. assumption.
        constructor 4. apply IHt1. assumption.
Qed.

End param_apart.

Require Import D5.

Fixpoint different {A : Type} (l1 l2 : list A) : Prop :=
match l1, l2 with
    | [], [] => False
    | [], _ => True
    | _, [] => True
    | h1 :: t1, h2 :: t2 => h1 <> h2 \/ different t1 t2
end.

Lemma different_spec :
  forall (A : Type) (l1 l2 : list A),
    l1 <> l2 <-> different l1 l2.
Proof.
  induction l1 as [| h1 t1]; cbn.
    destruct l2 as [| h2 t2]; cbn.
      tauto.
      firstorder congruence.
    destruct l2 as [| h2 t2]; cbn.
      firstorder congruence.
      split.
        Focus 2. destruct 1.
          congruence.
          destruct (IHt1 t2). firstorder congruence.
        intro. assert (~ (h1 = h2 /\ t1 = t2)).
          firstorder congruence.
Abort.

(** ** Techniczne aspekty rozstrzygalności 2 *)

Require Import Bool.

Print reflect.

Print BoolSpec.

Print CompareSpec.

Inductive Spec {A : Type} (P : A -> Prop) : A -> Prop :=
    | spec : forall x : A, P x -> Spec P x.

Ltac spec_aux H :=
match type of H with
    | Spec ?P ?x => destruct H as [x H], x
end.

Tactic Notation "spec" hyp(H) := spec_aux H.

Tactic Notation "spec" integer(n) :=
  intros until n;
match goal with
    | H : Spec _ _ |- _ => spec_aux H
end.

Goal
  forall (P Q : Prop) (b : bool),
    Spec (fun b : bool => if b then P else Q) b
      <->
    BoolSpec P Q b.
Proof.
  split.
    spec 1; constructor; assumption.
    destruct 1; constructor; assumption.
Qed.

Goal
  forall (P Q : Prop) (b : bool),
    Spec (fun b : bool => if b then P else Q) b
      <->
    BoolSpec P Q b.
Proof.
  split.
    spec 1; constructor; assumption.
    destruct 1; constructor; assumption.
Qed.

Lemma Spec_char :
  forall (A : Type) (P : A -> Prop) (x : A),
    P x <-> Spec P x.
Proof.
  split.
    intro. constructor. assumption.
    destruct 1. assumption.
Qed.

(** * Reflekcja w małej skali, czyli jak odbijać żeby się nie zmęczyć *)

Inductive even : nat -> Prop :=
    | even0 : even 0
    | evenSS : forall n : nat, even n -> even (S (S n)).

Function evenb (n : nat) : bool :=
match n with
    | 0 => true
    | 1 => false
    | S (S n') => evenb n'
end.

Lemma evenb_spec :
  forall n : nat, evenb n = true -> even n.
Proof.
  intros. functional induction evenb n.
    constructor.
    congruence.
    constructor. auto.
Qed.

Lemma wut : even 666.
Proof.
  apply evenb_spec. cbn. trivial. Show Proof.
Qed.

Compute wut.


(** Wrzucić tu przykład z porządkiem leksykograficznym z bloga Mondet.
    Dać też przykład z permutacjami? *)

(** * Poradnik hodowcy, czyli jak nie rozmnażać definicji *)

(** * Przerwa na reklamy: aksjomaty dotyczące sortu [Prop] *)

Definition PI : Prop :=
  forall (P : Prop) (x y : P), x = y.

Definition PropExt : Prop :=
  forall P Q : Prop, P <-> Q -> P = Q.

Definition UIP : Prop :=
  forall (A : Type) (x : A) (p : x = x), p = eq_refl.



(** * Sort [SProp], czyli zdania, ale takie jakby inne *)

Set Allow StrictProp.

Inductive sEmpty : SProp := .

Inductive sUnit : SProp :=
    | stt : sUnit.

Inductive seq {A : Type} (x : A) : A -> SProp :=
    | srefl : seq x x.

Goal forall A : Type, sEmpty -> A.
Proof.
  destruct 1.
Qed.

Goal
  forall {A : Type} (P : A -> Type) (x y : A),
    seq x y -> P x -> P y.
Proof.
  intros A P x y Hs Hp.
Abort.

Inductive Box (A : Type) : Prop :=
    | box : A -> Box A.

Print Box_sind.

Require Import SetIsType.

Lemma SetIsType : Set = Type.
Proof.
  reflexivity.
Qed.

(** * Metoda encode-decode, czyli o rozwiązaywaniu problemów, które sami sobie tworzymy *)

(** Jak powiedział śp. Stefan Kisielewski: "teoria typów bohatersko
    zwalcza problemy nieznane w żadnej innej teorii". *)

(** Okazuje się, że sortu [SProp] można całkiem efektywnie użyć do pokazywania,
    że coś jest zdaniem w sensie HoTTowym. Dzięki temu dowód jest krótszy o
    całe 33%. Całkiem nieźle. *)

Module encodedecode0.

Fixpoint code (n m : nat) : SProp :=
match n, m with
    | 0, 0 => sUnit
    | S _, 0 => sEmpty
    | 0, S _ => sEmpty
    | S n', S m' => code n' m'
end.

Fixpoint encode_aux (n : nat) : code n n :=
match n with
    | 0 => stt
    | S n' => encode_aux n'
end.

Definition encode {n m : nat} (p : n = m) : code n m :=
match p with
    | eq_refl => encode_aux n
end.

Fixpoint decode {n m : nat} : code n m -> n = m :=
match n, m with
    | 0, 0 => fun _ => eq_refl
    | 0, S _ => fun c => match c with end
    | S _, 0 => fun c => match c with end
    | S n', S m' => fun c => @f_equal _ _ S _ _ (@decode n' m' c)
end.

Lemma decode_encode :
  forall (n m : nat) (p : n = m),
    decode (encode p) = p.
Proof.
  destruct p; cbn.
  induction n as [| n']; cbn.
    reflexivity.
    rewrite IHn'. cbn. reflexivity.
Qed.

Lemma K_nat :
  forall (n : nat) (p : n = n), p = eq_refl.
Proof.
  intros.
  rewrite <- (decode_encode _ _ p).
  rewrite <- (decode_encode _ _ eq_refl).
  reflexivity.
Qed.

Lemma UIP_nat:
  forall {n m : nat} (p q : n = m), p = q.
Proof.
  intros.
  rewrite <- (decode_encode _ _ p), <- (decode_encode _ _ q).
  reflexivity.
Qed.

End encodedecode0.

Module encodedecode1.

Fixpoint code (n m : nat) : SProp :=
match n, m with
    | 0, _ => sUnit
    | _, 0 => sEmpty
    | S n', S m' => code n' m'
end.

Inductive gutle : nat -> nat -> Prop :=
    | gutle_0 : forall m : nat, gutle 0 m
    | gutle_SS : forall n m : nat, gutle n m -> gutle (S n) (S m).

Fixpoint encode {n m : nat} (H : gutle n m) : code n m :=
match H with
    | gutle_0 _ => stt
    | gutle_SS _ _ H' => encode H'
end.

Fixpoint decode (n m : nat) : code n m -> gutle n m :=
match n, m with
    | 0, _ => fun _ => gutle_0 m
    | n', 0 => fun c => match c with end
    | S n', S m' => fun c => gutle_SS _ _ (decode n' m' c)
end.

Fixpoint decode_encode
  {n m : nat} (H : gutle n m) : decode n m (encode H) = H.
Proof.
  destruct H; cbn.
    reflexivity.
    f_equal. apply decode_encode.
Defined.

Lemma isProp_gutle :
  forall {n m : nat} (p q : gutle n m), p = q.
Proof.
  intros.
  rewrite <- (decode_encode p), <- (decode_encode q).
  reflexivity.
Qed.

End encodedecode1.

Module encodedecode2.

Fixpoint code (n m : nat) : SProp :=
match n, m with
    | 0, _ => sUnit
    | _, 0 => sEmpty
    | S n', S m' => code n' m'
end.

Definition encode :
  forall {n m : nat}, n <= m -> code n m.
Proof.
  induction n as [| n'].
    cbn. constructor.
    destruct m as [| m'].
      inversion 1.
      cbn. intro. apply IHn'. apply le_S_n. assumption.
Defined.

Definition decode :
  forall {n m : nat}, code n m -> n <= m.
Proof.
  induction n as [| n'].
    intros. clear H. induction m as [| m'].
      constructor.
      constructor. assumption.
    destruct m as [| m']; cbn; intro.
      destruct H.
      apply le_n_S, IHn'. assumption.
Defined.

Fixpoint decode_encode
  {n m : nat} (H : n <= m) : decode (encode H) = H.
Proof.
  destruct H.
Abort.