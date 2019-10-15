(** * Rekursja przez iterację (TODO) *)

Require Import Omega.

Require Import List.
Import ListNotations.

Require Export Nat.

Require Import FunctionalExtensionality.

Definition collatzF (f : nat -> list nat) (n : nat) : list nat :=
match n with
    | 0 | 1 => [n]
    | _ => n :: if even n then f (div2 n) else f (1 + 3 * n)
end.

Module bad_div.

Definition divF (f : nat -> forall k : nat, 0 < k -> nat)
  (n k : nat) (H : 0 < k) : nat :=
match le_lt_dec k n with
    | left _ => S (f (n - k) k H)
    | right _ => 0
end.

Theorem divF_terminates :
  forall (n k : nat) (H : 0 < k),
    {v : nat | exists p : nat, forall n_iter : nat, p < n_iter ->
      forall f : forall n k : nat, 0 < k -> nat,
         iter n_iter divF f n k H = v}.
Proof.
  intros. generalize dependent n.
  apply well_founded_induction_type with lt.
    apply lt_wf.
    intros. case_eq (le_lt_dec k x); intro.
      destruct (H0 (x - k)) as [v Hv].
        abstract omega.
        exists (S v). destruct Hv as [p Hp]. exists (S p). intros.
          destruct (n_iter); cbn.
            abstract omega.
            unfold divF. rewrite H1. f_equal. apply Hp. abstract omega.
      exists 0. exists 0. intros. destruct n_iter; cbn.
        abstract omega.
        unfold divF. rewrite H1. trivial.
Defined.

Definition div (n k : nat) (H : 0 < k) : nat :=
  proj1_sig (divF_terminates n k H).

Theorem div_fix : div = divF div.
Proof.
Admitted.

Lemma div_equation :
  forall (n k : nat) (H : 0 < k),
    div n k H =
    if le_lt_dec k n then S (div (n - k) k H) else 0.
Proof.
Admitted.

End bad_div.

Module good_div.
Check iter.

Compute iter 10 S 1.
Fixpoint iter {A : Type} (n : nat) (f : A -> A) (x : A) : A :=
match n with
    | 0 => x
    | S n' => iter n' f (f x)
end.

Compute iter 10 S 1.



Inductive divG : nat -> nat -> nat -> Prop :=
  | divG_0 : forall n m : nat, n < S m -> divG n m 0
  | divG_1 : forall n m r : nat,
               n >= S m -> divG (n - S m) m r -> divG n m (S r).

Definition divF (div : nat -> nat -> nat) (n m : nat) : nat :=
  if n <? S m then 0 else S (div (n - S m) m).

Require Import Omega.

Theorem divF_terminates :
  forall n m : nat,
    {r : nat | exists fuel : nat,
      forall (more : nat) (f : nat -> nat -> nat),
        iter (fuel + more) divF f n m = r}.
Proof.
  apply (@well_founded_induction_type _ _ lt_wf (fun _ => forall m, _)).
  intros n IH m.
  case_eq (ltb n (S m)); intro.
    exists 0. exists 1. cbn. induction more; cbn; intros.
      unfold divF. rewrite H. reflexivity.
      apply IHmore.
    apply leb_complete_conv in H.
      destruct (IH (n - S m) ltac:(abstract omega) m) as (r & IH').
      exists (S r). destruct IH' as [fuel IH'].
      exists (S fuel). intros. cbn.
Abort.

End good_div.


Definition fac_F (f : nat -> nat) (n : nat) : nat :=
match n with
    | 0 => 1
    | S n' => n * f n'
end.

Definition facF_terminates :
  forall n : nat, {v : nat |
    exists p : nat, forall (k : nat) (f : nat -> nat),
      p < k -> iter k fac_F f n = v}.
Proof.
  induction n as [| n' [v H]].
    exists 1. exists 42. destruct k; cbn; intros.
      inversion H.
      trivial.
    exists (S n' * v). destruct H as [p H].
      exists (S p). destruct k; simpl; intros.
        inversion H0.
        rewrite H.
          trivial.
          omega.
Defined.

Definition fac (n : nat) : nat := proj1_sig (facF_terminates n).

Eval compute in fac 5.

Definition takeF {A : Type} (f : nat -> list A -> list A)
    (n : nat) (l : list A) : list A :=
match n with
    | 0 => []
    | S n' => match l with
        | [] => []
        | h :: t => h :: f n' t
    end
end.

Definition takeF_terminates : forall (A : Type) (n : nat) (l : list A),
    {v : list A | exists p : nat, forall (k : nat) (f : nat -> list A -> list A),
        p < k -> (iter k takeF f) n l = v}.
Proof.
  induction n as [| n'].
    exists []. exists 42. destruct k; cbn; intros.
      inversion H.
      trivial.
    destruct l as [| h t].
      exists []. exists 42. destruct k; cbn; intros.
        inversion H.
        trivial.
      destruct (IHn' t) as [v H]. exists (h :: v). destruct H as [p H].
        exists (S p). destruct k; simpl; intros.
          inversion H0.
          rewrite H.
            trivial.
            apply lt_S_n. assumption.
Defined.

Definition take {A : Type} (n : nat) (l : list A) : list A :=
  proj1_sig (takeF_terminates A n l).

Eval compute in take 3 [2; 3; 5; 7; 11].

Theorem take_spec1 : forall (A : Type) (l : list A),
    take 0 l = [].
Proof.
  unfold take. cbn. trivial.
Qed.

Theorem take_spec2 : forall (A : Type) (n : nat),
    take n [] = @nil A.
Proof.
  unfold take; destruct n; cbn; trivial.
Qed.

Theorem take_spec3 : forall (A : Type) (n : nat) (h : A) (t : list A),
    take (S n) (h :: t) = h :: take n t.
Proof.
  unfold take. intros.
  destruct (takeF_terminates A (S n) (h :: t)); cbn.
  destruct (takeF_terminates A n t); cbn.
  destruct e as [p H], e0 as [p' H'].
  specialize (H (S (S (max p p'))) (fun _ => id)). cbn in H.
  specialize (H' (S (max p p')) (fun _ => id)). cbn in H'.
  rewrite <- H, <- H'.
    trivial.
    unfold lt. apply Le.le_n_S. apply Max.le_max_r.
    unfold lt. apply Le.le_n_S. constructor. apply Max.le_max_l.
Qed.

Theorem take_eq : forall (A : Type) (n : nat) (l : list A),
    take n l = match n, l with
        | 0, _ => []
        | _, [] => []
        | S n', h :: t => h :: take n' t
    end.
Proof.
  destruct n as [| n'].
    intro. rewrite take_spec1. trivial.
    destruct l as [| h t].
      rewrite take_spec2. trivial.
      rewrite take_spec3. trivial.
Qed.

Theorem take_length : forall (A : Type) (n : nat) (l : list A),
    length (take n l) <= n.
Proof.
  induction n as [| n']; intros.
    rewrite take_spec1. trivial.
    destruct l as [| h t].
      rewrite take_spec2. cbn. omega.
      rewrite take_spec3. cbn. apply le_n_S. apply IHn'.
Restart.
  induction n as [| n']; intros; rewrite take_eq; cbn.
    trivial.
    destruct l; cbn.
      omega.
      destruct n'; cbn.
        omega.
        cbn in *. apply le_n_S. apply IHn'.
Qed.