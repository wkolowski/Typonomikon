(** * D3: Logika boolowska *)
 
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
Ltac solve_bool := intros; match goal with
    | b : bool |- _ => destruct b; clear b; solve_bool
    | _ => cbn; auto
end.
(* end hide *)

(** *** Właściwości negacji *)

Theorem negb_inv : negb (negb b) = b.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem negb_ineq : negb b <> b.
(* begin hide *)
Proof. destruct b; discriminate. Qed.
(* end hide *)

(** *** Eliminacja *)

Theorem andb_elim_l : b1 && b2 = true -> b1 = true.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem andb_elim_r : b1 && b2 = true -> b2 = true.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem andb_elim : b1 && b2 = true -> b1 = true /\ b2 = true.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem orb_elim : b1 || b2 = true -> b1 = true \/ b2 = true.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

(** *** Elementy neutralne *)

Theorem andb_true_neutral_l : true && b = b.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem andb_true_neutral_r : b && true = b.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem orb_false_neutral_l : false || b = b.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem orb_false_neutral_r : b || false = b.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

(** *** Anihilacja *)

Theorem andb_false_annihilation_l : false && b = false.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem andb_false_annihilation_r : b && false = false.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem orb_true_annihilation_l :  true || b = true.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem orb_true_annihilation_r :  b || true = true.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

(** *** Łączność *)

Theorem andb_assoc : b1 && (b2 && b3) = (b1 && b2) && b3.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem orb_assoc : b1 || (b2 || b3) = (b1 || b2) || b3.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

(** *** Przemienność *)

Theorem andb_comm : b1 && b2 = b2 && b1.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem orb_comm : b1 || b2 = b2 || b1.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

(** *** Rozdzielność *)

Theorem andb_dist_orb :
  b1 && (b2 || b3) = (b1 && b2) || (b1 && b3).
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem orb_dist_andb :
  b1 || (b2 && b3) = (b1 || b2) && (b1 || b3).
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

(** *** Wyłączony środek i niesprzeczność *)

Theorem andb_negb : b && negb b = false.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem orb_negb : b || negb b = true.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

(** *** Prawa de Morgana *)

Theorem negb_andb : negb (b1 && b2) = negb b1 || negb b2.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem negb_orb : negb (b1 || b2) = negb b1 && negb b2.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

(** *** [eqb], [xorb], [norb], [nandb] *)

Theorem eqb_spec : eqb b1 b2 = true -> b1 = b2.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem eqb_spec' : eqb b1 b2 = false -> b1 <> b2.
(* begin hide *)
Proof. destruct b1, b2; do 2 inversion 1. Qed.
(* end hide *)

Theorem xorb_spec :
  xorb b1 b2 = negb (eqb b1 b2).
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem xorb_spec' :
  xorb b1 b2 = true -> b1 <> b2.
(* begin hide *)
Proof. destruct b1, b2; do 2 inversion 1. Qed.
(* end hide *)

Theorem norb_spec :
  norb b1 b2 = negb (b1 || b2).
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem nandb_spec :
  nandb b1 b2 = negb (b1 && b2).
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

(** *** Różne *)

Theorem andb_eq_orb :
  b1 && b2 = b1 || b2 -> b1 = b2.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem all3_spec :
  (b1 && b2) || (negb b1 || negb b2) = true.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem noncontradiction_bool :
  negb (eqb b (negb b)) = true.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

Theorem excluded_middle_bool :
  b || negb b = true.
(* begin hide *)
Proof. solve_bool. Qed.
(* end hide *)

End boolean_functions.