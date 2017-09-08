(** * Z1: Teoria funkcji (alfa, TODO) *)

Require Import Arith.

Definition injective {A B : Type} (f : A -> B) : Prop :=
    forall x x' : A, f x = f x' -> x = x'.

(** TODO: trzeba tu coś napisać, ale na razie nie mam czasu. *)

Definition injective' {A B : Type} (f : A -> B) : Prop :=
    forall x x' : A, x <> x' -> f x <> f x'.

Theorem injective_is_injective' : forall (A B : Type) (f : A -> B),
    injective f -> injective' f.
(* begin hide *)
Proof.
  unfold injective, injective'; intros.
  intro. apply H0. apply H. assumption.
Qed.
(* end hide *)

Theorem injective'_is_injective_classic : forall (A B : Type) (f : A -> B)
    (EM : forall P : Prop, P \/ ~ P), injective' f -> injective f.
(* begin hide *)
Proof.
  unfold injective, injective'; intros.
  destruct (EM (x = x')).
    assumption.
    cut False.
      inversion 1.
      unfold not in H. apply (H x x').
        intro. apply H1. assumption.
        assumption.
Qed.
(* end hide *)

Theorem id_injective : forall A : Type,
    injective (fun x : A => x).
(* begin hide *)
Proof.
  intro. unfold injective. trivial.
Qed.
(* end hide *)

Theorem S_injective : injective (fun n : nat => S n).
(* begin hide *)
Proof.
  red. inversion 1. trivial.
Qed.
(* end hide *)

Theorem add_k_left_inj : forall k : nat,
    injective (fun n : nat => k + n).
(* begin hide *)
Proof.
  red. induction k as [| k']; simpl; intros.
    assumption.
    inversion H. apply IHk'. assumption.
Qed.
(* end hide *)

Theorem mul_k_inj : forall k : nat, k <> 0 ->
    injective (fun n : nat => k * n).
(* begin hide *)
Proof.
  red. intros k H x x'. generalize dependent k. generalize dependent x'.
  induction x as [| y]; induction x' as [| y']; simpl; intros.
    trivial.
    do 2 (rewrite mult_comm in H0; simpl in *). destruct k.
      contradiction H. trivial.
      simpl in H0. inversion H0.
    rewrite mult_0_r in H0. rewrite mult_comm in H0. simpl in H0. destruct k.
      contradiction H. trivial.
      simpl in H0. inversion H0.
    f_equal. apply (IHy y' k).
      assumption.
      SearchPattern (_ * S _ = _).
      do 2 rewrite mult_succ_r in H0. rewrite plus_comm in H0 at 1.
        replace (k * y' + k) with (k + k * y') in H0.
          assert (Hinj : injective (fun n : nat => k + n)).
            apply add_k_left_inj.
          red in Hinj. apply Hinj in H0. assumption.
        apply plus_comm.
Qed.
(* end hide *)

(* begin hide *)
Definition empty_A_to_A {A : Type} (x : sum Empty_set A) : A :=
match x with
    | inl e => match e with end
    | inr a => a
end. (* end hide *)
(* begin hide *)
(*Proof.
  destruct x.
    destruct e.
    assumption.
Qed.*)
(* end hide *)

Theorem pred_not_injective : ~ injective pred.
(* begin hide *)
Proof.
  unfold injective; intro. specialize (H 0 1 eq_refl). inversion H.
Qed.
(* end hide *)

Definition surjective {A B : Type} (f : A -> B) : Prop :=
    forall b : B, exists a : A, f a = b.

Theorem S_not_surjective : ~ surjective S.
(* begin hide *)
Proof.
  unfold surjective; intro. destruct (H 0). inversion H0.
Qed.
(* end hide *)

Definition bijective {A B : Type} (f : A -> B) : Prop :=
    injective f /\ surjective f.

Definition bijective' {A B : Type} (f : A -> B) : Prop :=
    forall b : B, exists! a : A, f a = b.

Theorem bijectives_equiv : forall (A B : Type) (f : A -> B),
    bijective f <-> bijective' f.
(* begin hide *)
Proof.
  unfold bijective, bijective', injective, surjective; split; intros.
    destruct H as [Hinj Hsur]. destruct (Hsur b) as [a H].
      exists a. red. split; try assumption. intros. apply Hinj.
      rewrite H, H0. reflexivity.
    split; intros.
      destruct (H (f x)) as [a Ha]. destruct Ha as [Ha1 Ha2].
        rewrite <- (Ha2 x).
          apply Ha2. rewrite H0. reflexivity.
          reflexivity.
      destruct (H b) as [a [H1 H2]]. exists a. assumption.
Qed.
(* end hide *)

Require Import List.
Import ListNotations.

Fixpoint unary (n : nat) : list unit :=
match n with
    | 0 => []
    | S n' => tt :: unary n'
end.

Theorem unary_bij : bijective unary.
(* begin hide *)
Proof.
  unfold bijective, injective, surjective. split.
    induction x as [| y]; induction x' as [| y']; simpl in *.
      trivial.
      inversion 1.
      inversion 1.
      inversion 1. f_equal. apply IHy. assumption.
    intro. exists (length b). induction b as [| h t]; simpl.
      trivial.
      destruct h. f_equal. assumption.
Qed.
(* end hide *)

