Require Import List.
Import ListNotations.

Fixpoint take {A : Type} (fuel n : nat) (l : list A) : list A :=
match fuel, n, l with
    | 0, _, _ => []
    | _, 0, _ => []
    | _, _, [] => []
    | S fuel', S n', h :: t => h :: take fuel' n' t
end.

Theorem take_fuel : forall (A : Type) (n : nat) (l : list A),
    n <= length l -> exists (fuel : nat) (l' : list A),
        take fuel n l = l' /\ length l' = n.
Proof.
  intros. exists (S n). generalize dependent l.
  induction n as [| n']; intros.
    exists []. simpl. split; trivial.
    destruct l as [| h t]; simpl in H.
      inversion H.
      apply le_S_n in H. destruct (IHn' t H) as [l' [H1 H2]].
        exists (h :: l'). split; try (simpl; auto; fail).
        replace (take (S (S n')) (S n') (h :: t))
        with (h :: take (S n') n' t).
          f_equal. assumption.
          simpl. trivial.
Qed.

Fixpoint take' {A : Type} (fuel n : nat) (l : list A) : option (list A) :=
match fuel, n, l with
    | 0, _, _ => None
    | _, 0, _ => Some []
    | _, _, [] => Some []
    | S fuel', S n', h :: t => liftM2 (@cons A) (ret h) (take' fuel' n' t)
end.

Theorem take'_fuel : forall (A : Type) (n : nat) (l : list A),
    {fuel : nat & {l' : list A | take' fuel n l = Some l'}}.
Proof.
  intros. exists (S n). generalize dependent l.
  induction n as [| n']; intros.
    simpl. exists []. trivial.
    destruct l as [| h t].
      exists []. simpl. trivial.
      destruct (IHn' t) as [l' H]. exists (h :: l').
        replace (take' (S (S n')) (S n') (h :: t))
        with (liftM2 (@cons A) (ret h) (take' (S n') n' t)).
          rewrite H. simpl. trivial.
          simpl. trivial.
Defined.

Eval compute in take' 2 1 [1; 2; 3].

Definition safeTake {A : Type} (n : nat) (l : list A) : list A.
    destruct (take'_fuel A n l) as [_ [result _]]. exact result.
Defined.

Eval compute in safeTake (pred 0) [1; 2; 3].

Fixpoint qs {A : Type} (le : A -> A -> bool) (fuel : nat) (l : list A)
    : option (list A) :=
match fuel, l with
    | 0, _ => None
    | _, [] => Some []
    | _, [x] => Some [x]
    | S fuel', h :: t =>
        let lesser := qs le fuel' (filter (fun x : A => le x h) t) in
        let greater := qs le fuel' (filter (fun x : A => negb (le x h)) t)
        in liftM2 (@app A) lesser (liftM2 (@app A) (ret [h]) greater)
end.

Definition leb := Compare_dec.leb.

Eval compute in qs leb 15 [5; 99; 15; 1; 1; 0; 2; 5; 6; 1; 13; 42; 55; 11].

Theorem qs_fuel : forall (A : Type) (le : A -> A -> bool) (l : list A),
    exists (fuel : nat) (l' : list A), qs le fuel l = Some l'.
Proof.
  intros. exists (S (length l)). induction l as [| h t].
    simpl. exists []. trivial.
    destruct IHt. simpl.