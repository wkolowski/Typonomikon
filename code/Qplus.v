(** * A simple canonical representation of rational numbers *)

(** * 1 From fractions to [Qplus] and back *)

(* W sumie [N] to następnić, jak [S] dla [nat]. *)
Inductive Qplus : Type :=
    | One : Qplus
    | N   : Qplus -> Qplus
    | D   : Qplus -> Qplus.

Print comparison.

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
    toQplus' p q =
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

Fixpoint fromQplus (q : Qplus) : nat * nat :=
match q with
    | One  => (1, 1)
    | N q' => let (p, q) := fromQplus q' in (p + q, q)
    | D q' => let (p, q) := fromQplus q' in (p, q + p)
end.

Compute fromQplus (toQplus (6, 7)).

Require Import Lia Arith.

(** TODO: prove that [fromQplus q] is always a reduced fraction. *)
Lemma fromQplus_reduced_fraction :
  forall (q : Qplus) (n m : nat),
    fromQplus q = (n, m) ->
      forall k n' m' : nat, n = k * n' -> m = k * m' -> k = 1.
Proof.
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
      unfold toQplus, fst, snd in *.
      rewrite toQplus'_eq, Nat.compare_succ in *.
Abort.

Lemma to_from :
  forall pq : nat * nat, fromQplus (toQplus pq) = pq.
Proof.
Abort.

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
    cmp_Qplus q1 q2 =
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

Definition qadd (q1 q2 : Qplus) : Qplus :=
  let (n1, m1) := fromQplus q1 in
  let (n2, m2) := fromQplus q2 in
    toQplus (n1 * m2 + n2 * m1, m1 * m2).

Definition qmul (q1 q2 : Qplus) : Qplus :=
match fromQplus q1, fromQplus q2 with
    | (n1, m1), (n2, m2) => toQplus (n1 * n2, m1 * m2)
end.

Compute fromQplus' (qadd (toQplus (2, 3)) (toQplus (3, 4))).
Compute fromQplus' (qmul (toQplus (2, 3)) (toQplus (3, 4))).

(** TODO: prove addition commutative and associative *)

Lemma qadd_comm :
  forall q1 q2 : Qplus,
    qadd q1 q2 = qadd q2 q1.
Proof.
  induction q1.
Admitted.

Lemma qadd_assoc :
  forall q1 q2 q3 : Qplus,
    qadd (qadd q1 q2) q3 = qadd q1 (qadd q2 q3).
Proof.
Admitted.

(** * 5 Encoding the whole rational field *)

Inductive Q : Set :=
    | Qneg  : Qplus -> Q
    | Qzero : Q
    | Qpos  : Qplus -> Q.

(** TODO: rozszerzyć operacje na [Qplus] na całe [Q]. *)

(** Kluczowa idea jest taka: jeżeli mamy jakiś typ [A] i jest
    on gówniany i trzeba go normalizować, żeby dostać kanonicznego
    reprezentanta, to można użyć śladu (ang. trace) algorytmu
    normalizującego, żeby uzyskać reprezentację typu [A], gdzie
    każdy element jest kanoniczny. *)