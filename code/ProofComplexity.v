Require Import Recdef Bool.

(**
  Let's define evenness as an inductive predicate:
  - 0 is even
  - if n is even, then 2 + n is even
*)
Inductive Even : nat -> Prop :=
| Even0 : Even 0
| EvenSS : forall n : nat, Even n -> Even (S (S n)).

(**
  Let's define a function that checks whether n is even:
  - 0 is even
  - 1 is not even
  - for 2 + n, check if n is even
*)
Function even (n : nat) : bool :=
match n with
| 0 => true
| 1 => false
| S (S n') => even n'
end.

(**
  Now we prove that if even n returns true, then n is even.
*)
Theorem Even_even :
  forall n : nat,
    even n = true -> Even n.
Proof.
  intros n Heq.
  (* The proof is by induction on n which follows the recursion scheme of even. *)
  functional induction (even n); cbn.
  - constructor. (* 0 is even *)
  - inversion Heq. (* true is not false *)
  - constructor. (* 2 + n' is even... *)
    now apply IHb. (* ... because of the induction hypothesis. *)
Defined.

(**
  We can prove evenness manually by building proof-terms using constructors
  EvenSS and Even0. Note that the first argument of EvenSS, which is n : nat,
  can be inferred, so we can omit it and write _.

  Interesting observation: a proof that a number n is even is basically the same
  thing as the number n/2, but in a different representation: Even0 is zero,
  EvenSS is successor, and we disregard the implicit argument of EvenSS.
*)
Definition e4 : Even 4 :=
  EvenSS _ (EvenSS _ Even0).

(**
  When we print the proof-term, the implicit arguments are displayed in full glory.
*)
Print e4.
(*
  e4 = EvenSS 2 (EvenSS 0 Even0)
     : Even 4
*)

(**
  We can also prove evenness with tactics. The tactic repeat may be handy for
  bigger numbers.
*)
Example e100 : Even 100.
Proof.
  constructor.
  constructor.
  repeat constructor.
Defined.

(** For 100, the proof is too big to be fully displayed. *)
Print e100.

(**
  We can also construct a proof of evenness by applying our theorem and then
  performing some computations.
*)
Example e100' : Even 100.
Proof.
  apply Even_even.
  cbn.
  reflexivity.
Defined.

(**
  When we print the proof that comes from the theorem, it always fits into a
  single line, but there's a trick: this is because we're using a decimal
  notation to display 100 succintly. In reality, the proof size does depend
  on the number, as the number is unary. However, it's still much shorter
  than the previous proofs.
*)
Print e100'.

(** Let's do some benchmarking now. *)

(** Defining x to be a proof of Even 1000 is quick - 0.049 secs for me. *)
Time Definition x : Even 1000 := Even_even 1000 eq_refl.

(** Computing a proof-term from our theorem takes longer - 0.962 sec for eager evaluation... *)
Time Definition y : Even 1000 := Eval cbv in (Even_even 1000 eq_refl).

(** ... and 2.385 secs for lazy evaluation *)
Time Definition z : Even 1000 := Eval cbn in (Even_even 1000 eq_refl).

(** Typechecking all three of these seems to take about equal time. *)
Time Check x. (* 0.012 secs *)
Time Check y. (* 0.012 secs *)
Time Check z. (* 0.012 secs *)

(**
  Displaying the unevaluated term is super quick, but displaying the full
  proof-terms takes quite proportional to their size.
*)
Time Print x. (* 0.024 secs *)
Time Print y. (* 1.427 secs *)
Time Print z. (* 1.471 secs *)

(**
  The time to typecheck the proofs coming from the theorem grows linearly in n,
  as expected from the definition of even.
*)
Time Check (Even_even 20 eq_refl).   (* 0.001 secs *)
Time Check (Even_even 40 eq_refl).   (* 0.002 secs *)
Time Check (Even_even 80 eq_refl).   (* 0.003 secs *)
Time Check (Even_even 160 eq_refl).  (* 0.006 secs *)
Time Check (Even_even 320 eq_refl).  (* 0.013 secs *)
Time Check (Even_even 640 eq_refl).  (* 0.020 secs *)
Time Check (Even_even 1280 eq_refl). (* 0.029 secs *)
Time Check (Even_even 2560 eq_refl). (* 0.049 secs *)

(**
  The time it takes to compute the low-level proof-term,
  which should be proportional to the proof-term's size,
  is quadratic in the size of the number.
*)
Time Compute (Even_even 20 eq_refl).   (* 0.003 secs *)
Time Compute (Even_even 40 eq_refl).   (* 0.008 secs *)
Time Compute (Even_even 80 eq_refl).   (* 0.022 secs *)
Time Compute (Even_even 160 eq_refl).  (* 0.062 secs *)
Time Compute (Even_even 320 eq_refl).  (* 0.171 secs *)
Time Compute (Even_even 640 eq_refl).  (* 0.698 secs *)
Time Compute (Even_even 1280 eq_refl). (* 2.731 secs *)
Time Compute (Even_even 2560 eq_refl). (* 11.365 secs *)

(**
  To sum up: for this particular example, the typechecking time for both
  the low-level proof-term and the proof coming from the theorem are about
  the same, but the space taken by the proof from the theorem is small compared
  to the space taken by the proof-term.

  There's a trade-off, but it looks quite favourable in this case. However,
  GPT tells me that typechecking the proof-term might be slightly faster than
  computing with even, because the typechecker is written in OCaml, so should
  be somewhat fast, whereas for Coq's evaluator, I'm not so sure how optimized
  it is under the hood.
*)