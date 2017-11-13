(** * R3: Taktyki i automatyzacja *)

(** Znasz już sporą część języka termów Coqa (zwanego Gallina) i potrafisz
    dowodzić przeróżnych właściwości programów. Po osięgnięciu pewnego
    poziomu zaawansowania i obycia (nazywanego zazwyczaj "mathematical
    maturity") ręczne klepanie dowodów przestaje być produktywne, a staje
    się nudne i męczące. Czas więc najwyższy nauczyć się pisać programy,
    które będą dowodzić poprawności innych programów za nas.

    W tym rozdziale poznamy podstawy języka [Ltac], który służy do tworzenia
    własnych taktyk. Jego składnię przedstawiono i skrupulatnie opisano tu:
    https://coq.inria.fr/refman/ltac.html

    Choć przykładowe twierdzenie znaczy więcej niż 0x3E8 słów i postaram się
    dokładnie zilustrować każdy istotny moim zdaniem konstrukt języka [Lac],
    to i tak polecam zapoznać się z powyższym linkiem. *)

(** * Kombinatory *)

Ltac existNatFrom n :=
  exists n || existNatFrom (S n).

Ltac existNat := existNatFrom O.

Goal exists m, m = 1.
  Fail (existNat; reflexivity).
Abort.

Ltac existNatFrom' n :=
  exists n + existNatFrom' (S n).

Ltac existNat' := existNatFrom' O.

Goal exists m, m = 15.
  existNat'; reflexivity.
Qed.

Theorem involution_unequal_negb : forall (f : bool -> bool) (b : bool),
    f (f b) = b -> f b <> b -> f b = negb b.
Proof.
  destruct b; simpl; intros.
    destruct (f true). contradiction H0; trivial. trivial.
    destruct (f false). trivial. contradiction H0; trivial.
Qed.


(** ** Notacje *)

Notation "b1 && b2" := (andb b1 b2).
Notation "b1 || b2" := (orb b1 b2).

(** Coq dysponuje również potężnym systemem notacji, które pozwalają
    nam uprościć sposób zapisywania funkcji, typów czy predykatów. *)

(** * Ltac — język taktyk *)

Theorem andb_dist_orb : forall b1 b2 b3 : bool,
    b1 && (b2 || b3) = (b1 && b2) || (b1 && b3).
Proof.
  destruct b1, b2, b3; simpl; reflexivity.
Qed.

(** Powyższe twierdzenie mówi, że koniunkcja boolowska jest rozdzielna
    względem alternatywy boolowskiej, ale dużo ważniejszy jest jego
    dowód. Myślę, że dostrzegasz już pewien schemat, jeżeli chodzi
    o dowodzenie właściwości funkcji boolowskich: sprowadza się to
    do rozbicia zmiennych na przypadki i obliczenia funkcji, w wyniku
    czego, jeżeli twierdzenie rzeczywiście jest prawdziwe, dostajemy
    pewną ilość tryiwalnych równości. *)

(** Gdybyśmy chcieli zdefiniować więcej funkcji boolowskich i dowodzić
    ich właściwości, moglibyśmy po prostu kopiować dowody i ewentualnie
    przystosowywać je do
    ilości występujących w twierdzeniach zmiennych boolowskich. Nie
    jest to jednak dobry pomysł. Tak jak programista nie powinien
    kopiować fragmentów kodu i wklejać ich gdzie indziej, tak też
    matematyk nie powinien kopiować i wklejać fragmentów dowodów.
    Programista dysponuje narzędziem, które pozwala mu tego uniknąć
    — jest nim możliwość pisania własnych funkcji/procedur, które
    pozwalają nadać kawałkowi kodu nazwę i odwoływać się do niego
    przy jej użyciu. Podobnym narzędziem dysponuje matematyk dowodzący
    w Coqu — jest nim możliwość pisania własnych taktyk w języku [Ltac].
    Dotychczas spotkaliśmy jedynie taktyki standardowe, jak [intro]
    czy [destruct], teraz zaś dowiemy się, jak pisać własne. *)

Ltac solve_bool := intros;
match goal with
    | b : bool |- _ => destruct b; solve_bool
    | _ => simpl; reflexivity
end.

Ltac solve_bool2 :=
match goal with
    | |- forall b : bool, _ => destruct b; solve_bool2
    | _ => simpl; reflexivity
end.

(** Definicje taktyk zaczynają się od słowa kluczowego [Ltac].
    W ciele definicji możemy używać taktyk oraz konstruktu
    [match goal with], który próbuje dopasować kontekst oraz
    cel do podanych niżej wzorców. Mają one postać
    [| kontekst |- cel => taktyka] lub podkreślnika,
    który oznacza "dopasuj cokolwiek". *)

(** Wyrażenie [kontekst] jest
    listą hipotez/wartości, których szukany w kontekście, tzn.
    jest postaci [x1 : A1, x2 : A2...], gdzie [A1] oznacza typ
    pierwszej wartości/hipotezy, a [x1] oznacza nazwę, którą
    nadajemy jej na potrzeby naszej taktyki (nie musi być ona
    taka sama jak rzeczywista nazwa występująca w twierdzeniu
    — możemy ją np. pominąć, używając podkreślnika [_]). *)

(** Wyrażenie [cel] jest typem, który reprezentuje dany cel,
    np. gdybyśmy szukali celów będących równościami, moglibyśmy
    jako [cel] podać wzorzec [_ = _]. *)

(** Po strzałce [=>] następuje nazwa taktyki, której chcemy
    użyć w danym przypadku. Ponieważ możemy użyć tylko jednej,
    zazwyczaj będziemy budować ją z wielu kombinatorów. *)

(** W naszym przypadku taktykę możemy podsumować tak:
    - wprowadź zmienne do kontekstu ([intros])
    - dopasuj cel i kontekst do podanych wzorców ([match goal with])
      - jeżeli w kontekście jest wartość typu [bool], nazwij ją [b],
        rozbij ją, a następnie wywołaj się rekurencyjnie
        ([| b : bool |- _ => destruct b; solve_bool])
      - w przeciwnym przypadku uprość cel i udowodnij trywialne
        równości ([| _ => simpl; reflexivity]) *)

Theorem andb_dist_orb' : forall b1 b2 b3 : bool,
    b1 && (b2 || b3) = (b1 && b2) || (b1 && b3).
Proof.
  solve_bool.
Restart.
  solve_bool2.
Qed.

Theorem not_true : forall b1 b2 : bool,
    b1 && b2 = b1 || b2.
Proof.
  try solve_bool.
Abort.

(** Jak widzimy, napisana przez nas taktyka nie jest magiczna
    i nie potrafi udowodnić nieprawdziwego twierdzenia. *)

(** * Automatyzacja *)

Hypotheses A B C D E F G H I J : Prop.

(** * Wyszukiwanie *)

Ltac search := try assumption; (left; search) + (right; search).

Theorem search_0 :
    I -> A \/ B \/ C \/ D \/ E \/ F \/ G \/ I \/ J.
Proof. search. Qed.

Theorem search_1 :
    I -> (((((((A \/ B) \/ C) \/ D) \/ E) \/ F) \/ G) \/ I) \/ J.
Proof. search. Qed.

Theorem search_2 :
    F -> (A \/ B) \/ (C \/ ((D \/ E \/ (F \/ G)) \/ H) \/ I) \/ J.
Proof. search. Qed.

Theorem search_3 :
    C -> (J \/ J \/ ((A \/ A \/ (C \/ D \/ (E \/ E))))).
Proof. search. Qed.

Theorem search_4 :
    A -> A \/ B \/ C \/ D \/ E \/ F \/ G \/ I \/ J.
Proof. search. Qed.

Theorem search_5 :
    D -> ~A \/ ((~B \/ (I -> I) \/ (J -> J)) \/ (D \/ (~D -> ~~D) \/ B \/ B)).
Proof. search. Qed.

Theorem search_6 :
    C -> (~~C /\ ~~~C) \/ ((C /\ ~C) \/ (~C /\ C) \/ (C -> C) \/ (C \/ ~C)).
Proof. search. Qed.

(** * Porządki *)

Ltac destr := intros; repeat
match goal with
    | H : _ /\ _ |- _ => destruct H
end; try assumption.

Theorem destruct_0 :
    A /\ B /\ C /\ D /\ E /\ F /\ G /\ H /\ I /\ J -> D.
Proof. destr. Qed.

Theorem destruct_1 :
    ((((((((A /\ B) /\ C) /\ D) /\ E) /\ F) /\ G) /\ H) /\ I) /\ J -> F.
Proof. destr. Qed.

Theorem destruct_2 :
    A /\ ~B /\ (C \/ C \/ C \/ C) /\ ((((D /\ I) /\ I) /\ I) /\ J) -> I.
Proof. destr. Qed.

(** Permutacje koniunktywe. *)

Ltac solve_and_perm := intros; repeat
match goal with
    | H : _ /\ _ |- _ => destruct H
end; repeat split; try assumption.

Theorem and_perm_0 : A /\ B /\ C /\ D /\ E /\ F /\ G /\ H /\ I /\ J ->
    J /\ I /\ H /\ G /\ F /\ E /\ D /\ C /\ B /\ A.
Proof. solve_and_perm. Qed.

Theorem and_perm_1 : A /\ B /\ C /\ D /\ E /\ F /\ G /\ H /\ I /\ J ->
    (((((((((A /\ B) /\ C) /\ D) /\ E) /\ F) /\ G) /\ H) /\ I) /\ J).
Proof. solve_and_perm. Qed.

Theorem and_perm_2 :
  (A /\ B) /\ (C /\ (D /\ E)) /\ (((F /\ G) /\ H) /\ I) /\ J ->
  (I /\ I /\ J) /\ ((A /\ B /\ (A /\ B)) /\ J) /\ (C /\ (E /\ (D /\ F /\ F))).
Proof. solve_and_perm. Qed.

(** Permutacje dysjunktywne. *)

(** Wskazówka: wykorzystaj taktykę search z ćw. 1 *)

Ltac solve_or_perm := intros; repeat
match goal with
    | H : _ \/ _ |- _ => destruct H
end; search.

Theorem or_perm : A \/ B \/ C \/ D \/ E \/ F \/ G \/ H \/ I \/ J ->
    (((((((((A \/ B) \/ C) \/ D) \/ E) \/ F) \/ G) \/ H) \/ I) \/ J).
Proof. solve_or_perm. Qed.

(** * Negacja *)

Fixpoint negn (n : nat) (P : Prop) : Prop :=
match n with
    | 0 => P
    | S n' => ~ negn n' P
end.

Eval simpl in negn 30.

Theorem dbl_neg : A -> ~~A.
Proof. unfold not. auto. Qed.

Ltac negtac := simpl; unfold not; intros;
match reverse goal with
    | H : _ -> False |- False => apply H; clear H; negtac
    | _ => try assumption
end.

Theorem neg_2_14 : negn 2 A -> negn 14 A.
Proof. negtac. Qed.

Theorem neg_100_200 : negn 100 A -> negn 200 A.
Proof. negtac. Qed.

Theorem neg_42_1000 : negn 42 A -> negn 200 A.
Proof. negtac. Qed.