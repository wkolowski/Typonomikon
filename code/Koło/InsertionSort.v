Print list.

Require Import List.
Import ListNotations.

Fixpoint ins
  {A : Type} (cmp : A -> A -> bool) (x : A) (l : list A) : list A :=
match l with
    | [] => [x]
    | h :: t =>
        if cmp x h then x :: h :: t else h :: ins cmp x t
end.

Fixpoint insertionSort
  {A : Type} (cmp : A -> A -> bool) (l : list A) : list A :=
match l with
    | [] => []
    | h :: t => ins cmp h (insertionSort cmp t)
end.

Require Import Arith.

Check leb.

Compute leb 1 1.

Compute insertionSort leb [6; 3; 4; 7; 1; 9].

Inductive sorted {A : Type} (cmp : A -> A -> bool) : list A -> Prop :=
    | sorted_nil : sorted cmp []
    | sorted_singl : forall x : A, sorted cmp [x]
    | sorted_cons :
        forall (x y : A) (t : list A),
          sorted cmp (y :: t) -> cmp x y = true ->
            sorted cmp (x :: y :: t).

Lemma example_sorted :
  sorted leb [1; 3; 4; 6; 7; 9].
Proof.
  apply sorted_cons.
    2: { cbn. reflexivity. }
  apply sorted_cons.
    2: { cbn. reflexivity. }
  apply sorted_cons.
    2: { cbn. reflexivity. }
  apply sorted_cons.
    2: { cbn. reflexivity. }
  apply sorted_cons.
    2: { cbn. reflexivity. }
  apply sorted_singl.
Qed.

Lemma example_sorted' :
  sorted leb [6; 3; 4; 7; 1; 9].
Proof.
  apply sorted_cons.
Abort.

Lemma ins_sorted :
  forall {A : Type} (cmp : A -> A -> bool) (x : A) (l : list A),
    sorted cmp l -> sorted cmp (ins cmp x l).
Proof.
  induction l.
    cbn. intros _. apply sorted_singl.
    intro H. cbn. case_eq (cmp x a); intro.
      apply sorted_cons.
        assumption.
        assumption.
Admitted.

Lemma insertionSort_sorted :
  forall {A : Type} (cmp : A -> A -> bool) (l : list A),
    sorted cmp (insertionSort cmp l).
Proof.
  induction l.
    cbn. apply sorted_nil.
    cbn. apply ins_sorted. assumption.
Qed.