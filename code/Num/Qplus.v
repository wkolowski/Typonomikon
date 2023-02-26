(** * A simple canonical representation of rational numbers *)

(** Kluczowa idea jest taka: jeżeli mamy jakiś typ [A] i jest
    on gówniany i trzeba go normalizować, żeby dostać kanonicznego
    reprezentanta, to można użyć śladu (ang. trace) algorytmu
    normalizującego, żeby uzyskać reprezentację typu [A], gdzie
    każdy element jest kanoniczny. *)

(** * 1 From fractions to [Qplus] and back *)

(* W sumie [N] to następnik, jak [S] dla [nat], a [D q] to  q/(q + 1). *)
Inductive Qplus : Type :=
| One : Qplus
| N   : Qplus -> Qplus
| D   : Qplus -> Qplus.

Unset Guard Checking.
Fixpoint toQplus' (p q : nat) {struct p} : Qplus :=
match Nat.compare p q with
| Lt => D (toQplus' p (q - p))
| Eq => One
| Gt => N (toQplus' (p - q) q)
end.
Set Guard Checking.

Lemma toQplus'_eq :
  forall p q : nat,
    toQplus' p q
      =
    match Nat.compare p q with
    | Lt => D (toQplus' p (q - p))
    | Eq => One
    | Gt => N (toQplus' (p - q) q)
    end.
Proof.
Admitted.

Lemma toQplus'_S_S :
  forall p q : nat,
    toQplus' (S p) (S q) = toQplus' p q.
Proof.
Admitted.

Definition toQplus (pq : nat * nat) : Qplus :=
  toQplus' (S (fst pq)) (S (snd pq)).

Compute toQplus (0, 1).
Compute toQplus (9, 10).
Compute toQplus (1, 2).
Compute toQplus (2, 3).
Compute toQplus (0, 3).

Fixpoint fromQplus (q : Qplus) : nat * nat :=
match q with
| One  => (1, 1)
| N q' => let (p, q) := fromQplus q' in (p + q, q)
| D q' => let (p, q) := fromQplus q' in (p, q + p)
end.

Compute fromQplus (toQplus (6, 7)).

Fixpoint frac (n : nat) : Qplus :=
match n with
| 0 => One
| S n' => D (frac n')
end.

Require Import List.
Import ListNotations.

Compute map (fun n => fromQplus (frac n)) [0; 1; 2; 3; 4; 5; 6; 7; 8; 9].

Require Import Lia Arith.

Definition ReducedFraction (n m : nat) : Prop :=
  forall k n' m' : nat,
    n = k * n' -> m = k * m' -> k = 1.

(* TODO *) Lemma fromQplus_ReducedFraction :
  forall (q : Qplus) (n m : nat),
    fromQplus q = (n, m) -> ReducedFraction n m.
Proof.
  unfold ReducedFraction.
  induction q as [| q' | q']; cbn.
    inversion 1; subst; intros. admit.
    destruct (fromQplus q'). inversion 1; intros; subst.
      assert (exists n'', n = k * n'').
        admit.
        destruct H1. eauto.
    destruct (fromQplus q'). inversion 1; intros; subst.
      assert (exists n'', n0 = k * n'').
        admit.
        destruct H0. eauto.
Admitted.

Lemma from_to :
  forall q : Qplus, toQplus (fromQplus q) = q.
Proof.
  induction q as [| q' | q'].
    cbn. reflexivity.
    simpl. destruct (fromQplus q') as [p q] eqn: Heq.
      {
        unfold toQplus, fst, snd in *.
        rewrite toQplus'_eq, Nat.compare_succ in *.
        destruct p as [| p'].
          rewrite plus_0_l. replace (q ?= q) with Eq.
Admitted.

Lemma to_from :
  forall n m : nat,
    ReducedFraction n m -> fromQplus (toQplus (n, m)) = (n, m).
Proof.
Admitted.

(** * 3 Order *)

Fixpoint cmp_Qplus (q1 q2 : Qplus) : comparison :=
match q1, q2 with
| One  , One   => Eq
| One  , D _   => Gt
| One  , N _   => Lt
| D _  , One   => Lt
| D q1', D q2' => cmp_Qplus q1' q2'
| D _  , N _   => Lt
| N _  , One   => Gt
| N _  , D _   => Gt
| N q1', N q2' => cmp_Qplus q1' q2'
end.

Lemma cmp_Qplus_wut :
  forall q1 q2 : Qplus,
    cmp_Qplus q1 q2
      =
    match cmp_Qplus q2 q1 with
    | Lt => Gt
    | Eq => Eq
    | Gt => Lt
    end.
Proof.
  induction q1; destruct q2; cbn; auto.
Qed.

Lemma cmp_Qplus_refl :
  forall q : Qplus,
    cmp_Qplus q q = Eq.
Proof.
  induction q; cbn; rewrite ?IHq; reflexivity.
Qed.

(** * 4 Primitive operations *)

Fixpoint inv (q : Qplus) : Qplus :=
match q with
| One  => One
| D q' => N (inv q')
| N q' => D (inv q')
end.

Definition fromQplus' (q : Qplus) : nat * nat :=
  let (n, m) := fromQplus q in (n - 1, m - 1).

Definition qpadd (q1 q2 : Qplus) : Qplus :=
  let (n1, m1) := fromQplus q1 in
  let (n2, m2) := fromQplus q2 in
    toQplus (n1 * m2 + n2 * m1, m1 * m2).

Definition qpmul (q1 q2 : Qplus) : Qplus :=
match fromQplus q1, fromQplus q2 with
| (n1, m1), (n2, m2) => toQplus (n1 * n2, m1 * m2)
end.

Compute fromQplus' (qpadd (toQplus (2, 3)) (toQplus (3, 4))).
Compute fromQplus' (qpmul (toQplus (2, 3)) (toQplus (3, 4))).

Lemma qpadd_comm :
  forall q1 q2 : Qplus,
    qpadd q1 q2 = qpadd q2 q1.
Proof.
  unfold qpadd; intros.
  destruct (fromQplus q1) as [n1 m1],
           (fromQplus q2) as [n2 m2].
  do 2 f_equal; lia.
Qed.

(* TODO *) Lemma qpadd_assoc :
  forall q1 q2 q3 : Qplus,
    qpadd (qpadd q1 q2) q3 = qpadd q1 (qpadd q2 q3).
Proof.
  unfold qpadd; intros.
  destruct (fromQplus q1) as [n1 m1],
           (fromQplus q2) as [n2 m2],
           (fromQplus q3) as [n3 m3].
  destruct (fromQplus (toQplus (n1 * m2 + n2 * m1, m1 * m2))) eqn: H12.
  destruct (fromQplus (toQplus (n2 * m3 + n3 * m2, m2 * m3))) eqn: H23.
  do 2 f_equal.
Admitted.

(** * 5 Encoding the whole rational field *)

Inductive Q : Set :=
| Qneg  : Qplus -> Q
| Qzero : Q
| Qpos  : Qplus -> Q.

(** TODO: rozszerzyć operacje na [Qplus] na całe [Q]. *)

Definition qneg (q : Q) : Q :=
match q with
| Qneg q' => Qpos q'
| Qzero   => Qzero
| Qpos q' => Qneg q'
end.

(*
Definition qadd (q1 q2 : Q) : Q :=
match q1, q2 with
| Qzero, _ => q2
| Qpos q1', Qpos q2' => Qpos (qpadd q1' q2')
*)