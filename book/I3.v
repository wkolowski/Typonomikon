(** * I3: Reflekcja - pusty *)

(** Chwilowo nic tu nie ma. *)

(* begin hide *)

(** * Small scale reflection *)

Inductive even : nat -> Prop :=
    | even0 : even 0
    | evenSS : forall n : nat, even n -> even (S (S n)).

(*
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

Goal even 666.
Proof.
  apply evenb_spec. cbn. trivial.
Qed.

Print Unnamed_thm.
Print evenb_spec.
*)

(** Wrzucić tu przykład z porządkiem leksykograficznym z bloga Mondet.
    Dać też przykład z permutacjami? *)

(** * [Ltac]: manipulowanie termami *)

(** TODO:
    - match expr
    - lazymatch expr
    - multimatch expr
    - type of term
    - eval redexpr
    - constr/uconstr/ltac
    - type_term ? *)

(** * Taktyki dla unifikacji *)

(** TODO:
    - [has_evar], [is_evar], [is_var]
    - [unify]
    - [constr_eq]
    - [instantiate]
    - [quote] *)

(** * Programowanie funkcyjne w [Ltac]u *)

(** Wstawić tutaj przykłady podobne do tych, które opisuje Chlipala. Być
    może jakiś większy development, tzn. zaprogramować listy w dwóch
    wersjach (zwykłe i zrobione produktem i unitem). *)

(** * Big scale reflection *)

(** Przykłady:
    - logika boolowska, czyli legitne [btauto]
    - permutacje
    - formuły logiczne
    - upraszczanie w monoidzie *)

(* end hide *)