(** * K3: Terminacja, nieterminacja i rekursja ogólna [TODO] *)

Require Import Lia.

(** * Monada nieterminacji *)

(** Da się zrobić kombinator punktu stałego i zamknąć go w monadę/modalność
    tak, żeby sprzeczność nie wyciekła na zewnątrz i żeby wszystko ładnie się
    liczyło, jeżeli wynik nie jest bottomem? TAK! *)

Module SafeFix.

Private Inductive Div (A : Type) : Type :=
| pure : A -> Div A.

Arguments pure {A} _.

Definition divmap {A B : Type} (f : A -> B) (x : Div A) : Div B :=
match x with
| pure a => pure (f a)
end.

Definition divbind {A B : Type} (x : Div A) (f : A -> Div B) : Div B :=
match x with
| pure a => f a
end.

Definition divjoin {A : Type} (x : Div (Div A)) : Div A :=
match x with
| pure (pure a) => pure a
end.

(** * Kombinator punktu stałego *)

Unset Guard Checking.
Fixpoint wutfix
  (u : unit) {A B : Type} (f : (A -> Div B) -> (A -> Div B)) (x : A) {struct u} : Div B :=
    f (wutfix u f) x.

Definition efix {A B : Type} (f : (A -> Div B) -> (A -> Div B)) (x : A) : Div B :=
  wutfix tt f x.
Set Guard Checking.

Arguments efix {A B} f x / : simpl nomatch.

Lemma unfix :
  forall {A B : Type} (f : (A -> Div B) -> (A -> Div B)) (x : A),
    efix f x = f (efix f) x.
Proof.
Admitted.

(** * Terminacja, nieterminacja *)

Private Inductive Terminates {A : Type} : Div A -> Prop :=
| terminates : forall x : A, Terminates (pure x).

Definition extract {A : Type} {x : Div A} (t : Terminates x) : A :=
match x with
| pure a => a
end.

Lemma Terminates_pure :
  forall {A : Type} (x : A),
    Terminates (pure x).
Proof.
  constructor.
Qed.

Lemma Terminates_divmap :
  forall {A B : Type} (f : A -> B) {x : Div A},
    Terminates x -> Terminates (divmap f x).
Proof.
  destruct 1; cbn; constructor.
Qed.

Lemma Terminates_divbind :
  forall {A B : Type} (f : A -> Div B) (x : Div A),
    Terminates x -> (forall x : A, Terminates (f x)) -> Terminates (divbind x f).
Proof.
  intros A B f x [] H. cbn. apply H.
Qed.

Private Inductive EvaluatesTo {A : Type} : Div A -> A -> Prop :=
| EvaluatesTo_pure : forall x : A, EvaluatesTo (pure x) x.

Definition eval {A : Type} {x : Div A} {y : A} (t : EvaluatesTo x y) : A :=
match x with
| pure a => a
end.

Lemma EvaluatesTo_eval :
  forall {A : Type} (da : Div A) (a : A) (e : EvaluatesTo da a),
    eval e = a.
Proof.
  now destruct e.
Qed.

Lemma EvaluatesTo_divmap :
  forall {A B : Type} (f : A -> B) {da : Div A} {a : A},
    EvaluatesTo da a -> EvaluatesTo (divmap f da) (f a).
Proof.
  now destruct 1; cbn.
Qed.

Lemma EvaluatesTo_det :
  forall {A : Type} {da : Div A} {a1 a2 : A},
    EvaluatesTo da a1 -> EvaluatesTo da a2 -> a1 = a2.
Proof.
  now do 2 inversion 1.
Qed.

Lemma Terminates_EvaluatesTo :
  forall {A : Type} (da : Div A) (a : A),
    EvaluatesTo da a -> Terminates da.
Proof.
  inversion 1; subst.
  now constructor.
Qed.

Lemma EvaluatesTo_extract :
  forall {A : Type} (da : Div A) (t : Terminates da),
    EvaluatesTo da (extract t).
Proof.
  destruct t; cbn.
  now constructor.
Qed.

End SafeFix.

(** * Przykłady *)

(** ** Algorytm Euklidesa *)

Import SafeFix.

Definition euclid (n m : nat) : Div nat :=
  efix (fun euclid '(n, m) =>
    match n with
    | 0 => pure m
    | _ => euclid (PeanoNat.Nat.modulo m n, n)
    end) (n, m).

Time Compute euclid (2 * 3 * 5 * 7) (2 * 7 * 11).

Lemma euclid_eq :
  forall n m : nat,
    euclid n m
      =
    match n with
    | 0 => pure m
    | _ => euclid (PeanoNat.Nat.modulo m n) n
    end.
Proof.
  intros.
  unfold euclid.
  rewrite unfix.
  reflexivity.
Defined.

Lemma Terminates_euclid :
  forall n m : nat, Terminates (euclid n m).
Proof.
  apply (well_founded_induction Wf_nat.lt_wf (fun n => forall m, Terminates (euclid n m))).
  intros n IH m.
  rewrite euclid_eq.
  destruct n as [| n'].
  - apply Terminates_pure.
  - apply IH. apply PeanoNat.Nat.mod_upper_bound. inversion 1.
Defined.

Definition euclid' (n m : nat) : nat :=
  extract (Terminates_euclid n m).

Compute euclid' 5 2.

Definition div (n m : nat) : Div nat :=
  efix (fun div '(n, m) =>
    if Nat.ltb n m
    then pure 0
    else divmap (plus 1) (div (n - m, m)))
  (n, m).

Compute div 51 12.

(** ** Dzielenie *)

Lemma div_eq :
  forall n m : nat,
    div n m
      =
    if Nat.ltb n m
    then pure 0
    else divmap (plus 1) (div (n - m) m).
(* begin hide *)
Proof.
  intros. unfold div. rewrite unfix. reflexivity.
Qed.
(* end hide *)

Lemma Terminates_div :
  forall n m : nat, 0 < m -> Terminates (div n m).
(* begin hide *)
Proof.
  apply (well_founded_induction Wf_nat.lt_wf
          (fun n => forall m, 0 < m -> Terminates (div n m))).
  intros n IH m Hlt.
  rewrite div_eq.
  destruct (Nat.ltb n m) eqn: Hltb.
  - apply Terminates_pure.
  - apply Terminates_divmap. apply IH.
    + apply PeanoNat.Nat.ltb_ge in Hltb. lia.
    + apply PeanoNat.Nat.ltb_nlt in Hltb. lia.
Qed.
(* end hide *)

Definition div' (n m : nat) (H : 0 < m) : nat :=
  extract (Terminates_div n m H).

(** ** Głupia funkcja... *)

Definition stupid (n : nat) : Div nat :=
  efix (fun stupid n => divmap (plus 1) (stupid (1 + n))) n.

Lemma stupid_eq :
  forall n : nat,
    stupid n
      =
    divmap (plus 1) (stupid (1 + n)).
Proof.
  intros. unfold stupid. rewrite unfix. reflexivity.
Qed.

Lemma nat_bounded_stupid :
  forall (f : nat -> nat),
    (forall n : nat, f n = 1 + f (1 + n)) ->
      forall n m : nat, n <= f m.
Proof.
  induction n as [| n']; cbn; intros m.
  - lia.
  - rewrite H. apply le_n_S. apply IHn'.
Qed.

Lemma EvaluatesTo_stupid :
  (forall n : nat, {m : nat | EvaluatesTo (stupid n) m}) -> False.
Proof.
  intros H.
  pose (e := fun n => eval (proj2_sig (H n))).
  assert (forall n : nat, n <= e 0).
  {
    intros n. apply nat_bounded_stupid.
    intros k. unfold e.
    rewrite !EvaluatesTo_eval.
    destruct (H k) eqn: I, (H (1 + k)) eqn: J; cbn.
    eapply EvaluatesTo_det; [eassumption |].
    rewrite stupid_eq.
    now apply EvaluatesTo_divmap.
  }
  specialize (H0 (1 + e 0)).
  lia.
Qed.

Lemma Terminates_stupid :
  ~ (forall n : nat, Terminates (stupid n)).
Proof.
  intros H.
  apply EvaluatesTo_stupid.
  intros n.
  exists (extract (H n)).
  now apply EvaluatesTo_extract.
Qed.

(** ** Funkcja Ackermanna *)

Definition ack' (n m : nat) : Div nat :=
  efix (fun ack' '(n, m) =>
    match n, m with
    | 0, _ => pure (1 + m)
    | Datatypes.S n', 0 => ack' (n', 1)
    | Datatypes.S n', Datatypes.S m' => divbind (ack' (n, m')) (fun r => ack' (n', r))
    end) (n, m).

Lemma ack'_eq :
  forall n m : nat,
    ack' n m
      =
    match n, m with
    | 0, _ => pure (1 + m)
    | Datatypes.S n', 0 => ack' n' 1
    | Datatypes.S n', Datatypes.S m' => divbind (ack' n m') (fun r => ack' n' r)
    end.
(* begin hide *)
Proof.
  intros. unfold ack'. rewrite unfix. reflexivity.
Qed.
(* end hide *)

Lemma Terminates_ack' :
  forall n m : nat,
    Terminates (ack' n m).
(* begin hide *)
Proof.
  induction n as [| n']; cbn; intros m.
  - apply Terminates_pure.
  - induction m as [| m'].
    + rewrite ack'_eq. apply IHn'.
    + rewrite ack'_eq. apply Terminates_divbind.
      * assumption.
      * assumption.
Qed.
(* end hide *)

Definition ack (n m : nat) : nat :=
  extract (Terminates_ack' n m).

Definition stupider (n : nat) : Div nat :=
  efix (fun stupid n => stupid (1 + n)) n.

Lemma stupider_eq :
  forall n : nat,
    stupider n = stupider (1 + n).
Proof.
  intros. unfold stupider. rewrite unfix. reflexivity.
Qed.