Require Import Omega.
Require Import List.
Import ListNotations.

Definition fac_F (f : nat -> nat) (n : nat) : nat :=
match n with
    | 0 => 1
    | S n' => n * f n'
end.

Fixpoint iter {A : Type} (n : nat) (f : A -> A) (x : A) : A :=
match n with
    | 0 => x
    | S n' => f (iter n' f x)
end.

Definition facF_terminates :
  forall n : nat, {v : nat |
    exists p : nat, forall (k : nat) (f : nat -> nat),
      p < k -> iter k fac_F f n = v}.
Proof.
  induction n as [| n' [v H]].
    exists 1. exists 42. destruct k; simpl; intros.
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
    exists []. exists 42. destruct k; simpl; intros.
      inversion H.
      trivial.
    destruct l as [| h t].
      exists []. exists 42. destruct k; simpl; intros.
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
  unfold take. simpl. trivial.
Qed.

Theorem take_spec2 : forall (A : Type) (n : nat),
    take n [] = @nil A.
Proof.
  unfold take; destruct n; simpl; trivial.
Qed.

Theorem take_spec3 : forall (A : Type) (n : nat) (h : A) (t : list A),
    take (S n) (h :: t) = h :: take n t.
Proof.
  unfold take. intros.
  destruct (takeF_terminates A (S n) (h :: t)); simpl.
  destruct (takeF_terminates A n t); simpl.
  destruct e as [p H], e0 as [p' H'].
  specialize (H (S (S (max p p'))) (fun _ => id)). simpl in H.
  specialize (H' (S (max p p')) (fun _ => id)). simpl in H'.
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
      rewrite take_spec2. simpl. omega.
      rewrite take_spec3. simpl. apply le_n_S. apply IHn'.
Restart.
  induction n as [| n']; intros; rewrite take_eq; simpl.
    trivial.
    destruct l; simpl.
      omega.
      destruct n'; simpl.
        omega.
        simpl in *. apply le_n_S. apply IHn'.
Qed.