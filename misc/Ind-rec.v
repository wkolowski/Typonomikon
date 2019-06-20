(**

  If there was induction-recursion in Coq, we could use it to define
  McCarthy's f91 function simultaneously with its domain predicate
  (living in Type, not Prop - TODO improve).

  Inductive dom : nat -> Type :=
      | dom_gt100 : forall n : nat, 100 < n -> dom n
      | dom_le100 :
          forall n : nat, n <= 100 ->
            forall d : dom (n + 11), dom (f (n + 11) d) -> dom n

  with Fixpoint f (n : nat) (d : dom n) : nat :=
  match d with
      | dom_gt100 n H => n - 10
      | dom_le100 n H d1 d2 => f (f (n + 11) d1) d2
  end.

  We can use our axiomatic encoding to prove some theorems, like for all
  n <= 100 we have f n = 91.

  The real question is, however, different: does induction-recursion solve
  any problems at all? Could we define dom and f without it?
*)

Variables
  (dom : nat -> Type)
  (f : forall n : nat, dom n -> nat)
  (dom_gt100 : forall n : nat, 100 < n -> dom n)
  (dom_le100 :
    forall n : nat, n <= 100 ->
      forall d : dom (n + 11), dom (f (n + 11) d) -> dom n)
  (f_eq1 :
    forall (n : nat) (H : 100 < n), f n (dom_gt100 n H) = n - 10)
  (f_eq2 :
    forall
      (n : nat) (H : n <= 100)
      (d1 : dom (n + 11)) (d2 : dom (f (n + 11) d1)),
        f n (dom_le100 n H d1 d2) = f (f (n + 11) d1) d2)
  (ind :
    forall
      (P : forall n : nat, dom n -> Type)
      (H1 : forall (n : nat) (H : 100 < n), P n (dom_gt100 n H))
      (H2 :
        forall
          (n : nat) (H : n <= 100)
          (d1 : dom (n + 11)) (d2 : dom (f (n + 11) d1)),
            P (n + 11) d1 -> P (f (n + 11) d1) d2 ->
              P n (dom_le100 n H d1 d2)),
      forall (n : nat) (d : dom n), P n d).

Lemma case :
  forall
    (P : forall n : nat, dom n -> Type)
    (H1 : forall (n : nat) (H : 100 < n), P n (dom_gt100 n H))
    (H2 :
      forall
        (n : nat) (H : n <= 100)
        (d1 : dom (n + 11)) (d2 : dom (f (n + 11) d1)),
          P n (dom_le100 n H d1 d2)),
    forall (n : nat) (d : dom n), P n d.
Proof.
  intros until 2. apply ind.
    assumption.
    intros. apply H2.
Defined.

Lemma dom_inv :
  forall (n : nat) (d : dom n),
    {H : 100 < n | d = dom_gt100 n H} +
    {H : n <= 100 &
      {d1 : dom (n + 11) &
      {d2 : dom (f (n + 11) d1) | d = dom_le100 n H d1 d2}}}.
Proof.
  apply ind.
    intros. left. exists H. reflexivity.
    intros. right. exists H, d1, d2. reflexivity.
Defined.

Require Import Omega.

Lemma f_spec :
  forall (n : nat) (d : dom n),
    n <= 100 -> f n d = 91.
Proof.
  apply (ind (fun n d => n <= 100 -> f n d = 91)).
    intros n H H'. omega.
    intros n H d1 d2 IH1 IH2 _.
      destruct (dom_inv _ d1) as [[H' eq] | (H' & d1' & d2' & eq)].
        Focus 2. rewrite f_eq2. apply IH2. rewrite IH1.
          omega.
          assumption.
        destruct (dom_inv _ d2) as [[H'' eq'] | (H'' & d1'' & d2'' & eq')].
          Focus 2. rewrite f_eq2. apply IH2. assumption.
            rewrite f_eq2, eq', f_eq1, eq, f_eq1 in *.
            clear IH1 eq eq' H' H''.
            (* Either n = 100 and then 100 + 11 - 10 - 10 = 111 - 20 = 91
               or n < 100 and then n + 11 - 10 = n + 1 <= 100 and the
               result follows from IH2. omega knows this *)
            omega.
Defined.