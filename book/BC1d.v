(** * BC1d: Logika boolowska *)

(** Zadania z funkcji boolowskich, sprawdzające radzenie sobie w pracy
    z enumeracjami, definiowaniem funkcji przez dopasowanie do wzorca
    i dowodzeniem przez rozbicie na przypadki.

    Chciałem, żeby nazwy twierdzeń odpowiadały tym z biblioteki standardowej,
    ale na razie nie mam siły tego ujednolicić. *)

Section boolean_functions.
Variables b b1 b2 b3 : bool.

(** * Definicje *)

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

(** * Twierdzenia *)

(** Udowodnij, że zdefiniowane przez ciebie funkcje mają spodziewane
    właściwości. *)

(* begin hide *)
Ltac solve_bool := intros;
match goal with
| b : bool |- _ => destruct b; clear b; solve_bool
| _ => cbn; auto
end.
(* end hide *)

(** ** Właściwości negacji *)

Lemma negb_inv : negb (negb b) = b.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Lemma negb_ineq : negb b <> b.
(* begin hide *)
Proof. destruct b; discriminate. Qed.
(* end hide *)

(** ** Eliminacja *)

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

(** ** Elementy neutralne *)

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

(** ** Anihilacja *)

Lemma andb_false_l : false && b = false.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Lemma andb_false_r : b && false = false.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Lemma orb_true_l :  true || b = true.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Lemma orb_true_r :  b || true = true.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

(** ** Łączność *)

Lemma andb_assoc : b1 && (b2 && b3) = (b1 && b2) && b3.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Lemma orb_assoc : b1 || (b2 || b3) = (b1 || b2) || b3.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

(** ** Przemienność *)

Lemma andb_comm : b1 && b2 = b2 && b1.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Lemma orb_comm : b1 || b2 = b2 || b1.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

(** ** Rozdzielność *)

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

(** ** Wyłączony środek i niesprzeczność *)

Lemma andb_negb : b && negb b = false.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Lemma orb_negb : b || negb b = true.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

(** ** Prawa de Morgana *)

Lemma negb_andb : negb (b1 && b2) = negb b1 || negb b2.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Lemma negb_orb : negb (b1 || b2) = negb b1 && negb b2.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

(** ** [eqb], [xorb], [norb], [nandb] *)

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

(** ** Różne *)

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

(** * Zadania *)

(** **** [majority] *)

(** Zdefiniuj funkcję [majority], która bierze 3 wartości boolowskie i zwraca
    wartość boolowską. Jeśli co najmniej dwa z trzech argumentów to [true], to
    wynikiem funkcji jest [true]. W przeciwnym wypadku wynikiem jest [false].

    Użyj wyłącznie dopasowania do wzorca - nie używaj żadnych zdefiniowanych
    wcześniej funkcji.

    Następnie udowodnij kilka właściwości funkcji [majority]. *)

Definition majority (a b c : bool) : bool :=
match a, b, c with
| true , true , true  => true
| x    , false, true  => x
| true , y    , false => y
| false, true , z     => z
| false, false, false => false
end.

Lemma majority_spec :
  forall a b c : bool,
    majority a b c = andb (orb a b) (andb (orb b c) (orb c a)).
(* begin hide *)
Proof.
  destruct a, b, c; cbn; reflexivity.
Qed.
(* end hide *)

Lemma majority_spec' :
  forall a b c : bool,
    majority a b c = orb (andb a b) (orb (andb b c) (andb c a)).
(* begin hide *)
Proof.
  destruct a, b, c; cbn; reflexivity.
Qed.
(* end hide *)

Lemma negb_majority :
  forall a b c : bool,
    negb (majority a b c) = majority (negb a) (negb b) (negb c).
(* begin hide *)
Proof.
  destruct a, b, c; cbn; reflexivity.
Qed.
(* end hide *)

Lemma majority_orb :
  forall a1 a2 b c : bool,
    majority (orb a1 a2) b c = orb (majority a1 b c) (majority a2 b c).
(* begin hide *)
Proof.
  destruct a1, a2, b, c; cbn; reflexivity.
Qed.
(* end hide *)

Lemma majority_andb :
  forall a1 a2 b c : bool,
    majority (andb a1 a2) b c = andb (majority a1 b c) (majority a2 b c).
(* begin hide *)
Proof.
  destruct a1, a2, b, c; cbn; reflexivity.
Qed.
(* end hide *)

Lemma majority_permute :
  forall a b c : bool,
    majority a b c = majority b c a.
(* begin hide *)
Proof.
  destruct a, b, c; cbn; reflexivity.
Qed.
(* end hide *)

Lemma majority_swap :
  forall a b c : bool,
    majority a b c = majority b a c.
(* begin hide *)
Proof.
  destruct a, b, c; cbn; reflexivity.
Qed.
(* end hide *)

(** **** Logika ternarna *)

(** Wymyśl logikę trójwartościową. W tym celu:
    - Zdefiniuj trójelementowy typ [bool3], którego elementy reprezentować będą
      wartości logiczne
    - Zastanów się, co reprezentuje trzeci element: "jednocześnie prawda i fałsz",
      "ani prawda, ani fałsz", "nie wiadomo", "pies zjadł mi wartość logiczną"?
    - Zdefiniuj funkcje [negb3] (negacja), [andb3] (koniunkcja), [orb3] (dysjunkcja)
      i udowodnij, że mają takie właściwości, jak odpowiadające im funkcje
      boolowskie, tj. koniunkcja i dysjunkcja są łączne, przemienne, rozdzielne
      względem siebie nawzajem, etc., zaś negacja jest inwolutywna i reaguje w
      odpowiedni sposób z koniunkcją i dysjunkcją.
*)

(* begin hide *)
Module ternary_unknown.

Inductive bool3 : Set :=
| true : bool3
| false : bool3
| unknown : bool3.

Definition negb3 (b : bool3) : bool3 :=
match b with
| true => false
| false => true
| unknown => unknown
end.

Definition andb3 (b1 b2 : bool3) : bool3 :=
match b1, b2 with
| true, true => true
| false, _ => false
| _, false => false
| _, _ => unknown
end.

Definition orb3 (b1 b2 : bool3) : bool3 :=
match b1, b2 with
| false, false => false
| true, _ => true
| _, true => true
| _, _ => unknown
end.

Ltac solve_bool3 := intros;
match reverse goal with
| b : bool3 |- _ => destruct b; solve_bool3
| _ => cbn; reflexivity
end.

Notation "b1 & b2" := (andb3 b1 b2) (at level 40).
Notation "b1 | b2" := (orb3 b1 b2) (at level 40).

Lemma andb3_comm :
  forall b1 b2 : bool3, b1 & b2 = b2 & b1.
Proof. solve_bool3. Qed.

Lemma orb3_comm :
  forall b1 b2 : bool3, b1 | b2 = b2 | b1.
Proof. solve_bool3. Qed.

Lemma andb3_dist_orb3 :
  forall b1 b2 b3 : bool3,
    b1 & (b2 | b3) = (b1 & b2) | (b1 & b3).
Proof. solve_bool3. Qed.

Lemma orb3_dist_andb3 :
  forall b1 b2 b3 : bool3,
    b1 | (b2 & b3) = (b1 | b2) & (b1 | b3).
Proof. solve_bool3. Qed.

Lemma andb3_true_neutral_l :
  forall b : bool3, andb3 true b = b.
Proof. solve_bool3. Qed.

Lemma andb3_true_neutral_r :
  forall b : bool3, andb3 b true = b.
Proof. solve_bool3. Qed.

End ternary_unknown.
(* end hide *)