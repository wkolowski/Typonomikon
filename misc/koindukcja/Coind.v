Require Import List.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) .. ).

Variable A : Type.

CoInductive stream (T : Type) : Type :=
    | cons : T -> stream T -> stream T.

Arguments cons [T] _ _.

CoFixpoint nats : stream nat := (cofix f (n : nat) := cons n (f (S n))) 0.

Fixpoint take {T : Type} (n : nat) (s : stream T) : list T :=
    match n, s with
    | 0, _ => nil
    | S n', cons v s' => v :: (take n' s')
end.

CoFixpoint facts : stream nat :=
(cofix f (r n : nat) := cons r (f (r * (S n)) (S n))) 1 0.

CoFixpoint infinite (n : nat) : stream nat := cons n (infinite n).

Compute take 455 nats.

Compute take 45 (infinite 5).

Compute take 9 facts.

Definition injection {A B : Type} (f : A -> B) :=
forall a b : A, f a = f b -> a = b.

Theorem injection_id : forall T : Type, injection (fun x : T => x).
unfold injection. intros. apply H.
Qed.

Definition surjection {A B : Type} (f : A -> B) :=
forall b : B, exists a : A, f a = b.

Theorem surjection_id : forall T : Type, surjection (fun x : T => x).
unfold surjection. intros. exists b. trivial.
Qed.

Theorem S_inj : injection S.
unfold injection. intros. inversion H. trivial.
Qed.

Definition bijection {A B : Type} (f : A -> B) := injection f /\ surjection f.