(** * Seminar2: Proof by reflection *)

(** Nothing fancy yet. *)

(** * Small scale reflection *)

(* begin hide *)

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

Goal even 666.
Proof.
  apply evenb_spec. cbn. trivial.
Qed.

Print Unnamed_thm.
Print evenb_spec.

(** Wrzucić tu przykład z porządkiem leksykograficznym z bloga Mondet.
    Dać też przykład z permutacjami? *)

(** * Matching terms *)

(** TODO:
    - match expr
    - lazymatch expr
    - multimatch expr
    - type of term
    - eval redexpr
    - constr/uconstr/ltac
    - type_term ?

    Taktyki: [has_evar], [is_evar], [is_var], [unify], [constr_eq],
    [instantiate], [quote] *)

(** * Functional programming in Ltac *)

(** * Big scale reflection *)

(** Wklej tu przykład z permutacjami, wyrażenia boolowskie, formuły
    logiczne i upraszczanie w monoidzie. *)

(* end hide *)