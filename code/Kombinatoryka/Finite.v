From Typonomikon Require Import D5 BetterFinite.

Import ExactlyFinite.

Require Import Equality.

#[refine]
#[export]
Instance ExactlyFinite_bool : ExactlyFinite bool :=
{|
  elems := [false; true];
|}.
Proof.
  destruct x; repeat constructor.
  intros. dependent destruction e1; dependent destruction e2.
    reflexivity.
    exfalso. inv e2. inv H0.
    exfalso. inv e1. inv H0.
    f_equal. dependent destruction e1; dependent destruction e2.
      reflexivity.
      exfalso. inv e2.
      exfalso. inv e1.
      f_equal. inv e1.
Defined.

Lemma Elem_map :
  forall {A B : Type} (f : A -> B) (x : A) (l : list A),
    Elem x l -> Elem (f x) (map f l).
Proof.
  induction l as [| h t]; cbn; intros.
    dependent destruction X.
    dependent destruction X; constructor. apply IHt. assumption.
Defined.

Lemma Elem_map_inv :
  forall {A B : Type} (f : A -> B) (b : B) (l : list A),
    Elem b (map f l) -> {a : A | f a = b}.
Proof.
  induction l as [| h t]; cbn; intros.
    inv X.
    inv X.
      exists h. reflexivity.
      apply IHt. assumption.
Qed.

Lemma Elem_map_Some :
  forall {A : Type} (a : A) (l : list A),
    Elem (Some a) (map Some l) -> Elem a l.
Proof.
  induction l as [| h t]; cbn; intros.
    dependent destruction X.
    dependent destruction X; constructor. apply IHt. assumption.
Defined.

Lemma Elem_map__Elem_map_Some :
  forall {A : Type} (a : A) (l : list A) (H : Elem a l),
    Elem_map_Some a l (Elem_map Some a l H) = H.
Proof.
  dependent induction H.
Admitted.

Lemma Elem_map_Some__Elem_map :
  forall {A : Type} (a : A) (l : list A) (H : Elem (Some a) (map Some l)),
    Elem_map Some a l (Elem_map_Some a l H) = H.
Proof.
  induction l as [| h t]; cbn; intros.
    inv H.
    dependent destruction H.
Admitted.

#[refine]
#[export]
Instance Finite_option
  {A : Type} (FA : ExactlyFinite A) : ExactlyFinite (option A) :=
{|
  elems := None :: map Some (@elems _ FA);
|}.
Proof.
  all: destruct FA as [els H1 H2]; cbn.
    destruct x as [a |].
      constructor. apply Elem_map. apply H1.
      constructor.
    destruct x as [a |]; intros.
      2: {
        dependent destruction e1; dependent destruction e2.
          reflexivity.
          exfalso. apply Elem_map_inv in e2. destruct e2. congruence.
          exfalso. apply Elem_map_inv in e1. destruct e1. congruence.
          exfalso. apply Elem_map_inv in e2. destruct e2. congruence.
      }
      {
        dependent destruction e1; dependent destruction e2. f_equal.
        rewrite <- (Elem_map_Some__Elem_map _ _ e1), <- (Elem_map_Some__Elem_map _ _ e2).
        f_equal. apply H2.
      }
Defined.

Fixpoint sum (l : list nat) : nat :=
match l with
| [] => 0
| h :: t => h + sum t
end.

Lemma elem_sum :
  forall {n : nat} {l : list nat},
    Elem n l -> n <= sum l.
Proof.
  induction 1; cbn; lia.
Qed.

Lemma nat_not_Finite :
  ExactlyFinite nat -> False.
Proof.
  intros [els H1 H2].
  specialize (H1 (S (sum els))).
  apply elem_sum in H1.
  lia.
Qed.

Lemma join_elem_length :
  forall {A : Type} {l : list A} {ll : list (list A)},
    Elem l ll -> length l <= length (join ll).
Proof.
  induction 1; cbn;
  rewrite length_app;
  lia.
Qed.

Lemma list_not_Finite :
  forall A : Type,
    ExactlyFinite (list A) -> A -> False.
Proof.
  intros A [els H1 H2] x.
  specialize (H1 (x :: join els)).
  apply join_elem_length in H1; cbn in H1.
  lia.
Qed.