Require Import Bool.

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

(** * Porządki *)

Ltac destr := intros; repeat
match goal with
    | H : _ /\ _ |- _ => destruct H
end; try assumption.

Hypotheses A B C D E F G H I J : Prop.

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
(* end hide *)