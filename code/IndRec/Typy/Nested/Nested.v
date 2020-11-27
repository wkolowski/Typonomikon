(* Pomysł na Complete wzięty stąd: http://comonad.com/reader/wp-content/uploads/2010/04/Finger-Trees.pdf *)

Require Import Recdef.

Inductive Complete (A : Type) : Type :=
    | Empty : Complete A
    | Layer : A -> Complete (A * A) -> Complete A.

Arguments Empty {A}.
Arguments Layer {A} _ _.

Function leftmost {A : Type} (t : Complete A) : option A :=
match t with
    | Empty      => None
    | Layer v t' =>
        match leftmost t' with
            | None   => Some v
            | Some (l, _) => Some l
        end
end.

Fixpoint rightmost {A : Type} (t : Complete A) : option A :=
match t with
    | Empty      => None
    | Layer v t' =>
        match rightmost t' with
            | None   => Some v
            | Some (_, r) => Some r
        end
end.

Fixpoint map {A B : Type} (f : A -> B) (t : Complete A) : Complete B :=
match t with
    | Empty      => Empty
    | Layer v t' => Layer (f v) (map (fun '(x, y) => (f x, f y)) t')
end.

Definition swap {A B : Type} (p : A * B) : B * A :=
match p with
    | (x, y) => (y, x)
end.

Fixpoint mirror {A : Type} (t : Complete A) : Complete A :=
match t with
    | Empty      => Empty
    | Layer v t' => Layer v (map swap (mirror t'))
end.

Fixpoint nums (n : nat) : Complete nat :=
match n with
    | 0    => Empty
    | S n' => Layer n (map (fun x => (x, x)) (nums n'))
end.

Definition test : Complete nat :=
  Layer 0 (
  Layer (0, 1) (
  Layer (0, 1, (2, 3)) (
  Empty))).

Compute nums 5.
Compute mirror (nums 5).
Compute mirror test.

Require Import FunctionalExtensionality.

Lemma map_map :
  forall {A B C : Type} (f : A -> B) (g : B -> C) (t : Complete A),
    map g (map f t) = map (fun x => g (f x)) t.
Proof.
  intros until t. revert B C f g.
  induction t; cbn; intros.
    reflexivity.
    rewrite IHt. repeat f_equal.
      extensionality x. destruct x. reflexivity.
Qed.

Lemma leftmost_map :
  forall {A B : Type} (f : A -> B) (t : Complete A),
    leftmost (map f t) =
      match leftmost t with
          | None   => None
          | Some a => Some (f a)
      end.
Proof.
  intros. revert B f.
  induction t; cbn; intros.
    reflexivity.
    rewrite IHt. destruct (leftmost t).
      destruct p. reflexivity.
      reflexivity.
Qed.

Lemma leftmost_mirror :
  forall {A : Type} (t : Complete A),
    leftmost (mirror t) = rightmost t.
Proof.
  induction t; cbn.
    reflexivity.
    rewrite leftmost_map, IHt.
      destruct (rightmost t) as [[] |]; cbn; reflexivity.
Qed.