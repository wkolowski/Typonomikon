Require Import List.
Import ListNotations.

Inductive Tree (A : Type) : Type :=
    | Node : A -> list (Tree A) -> Tree A.

Arguments Node {A} _ _.

Inductive mirrorFG
  {A : Type} (f : Tree A -> Tree A) : Tree A -> Tree A -> Prop :=
    | mirrorFG_0 :
        forall (x : A) (ts : list (Tree A)),
          mirrorFG f (Node x ts) (Node x (rev (map f ts))).

Definition mirror_spec
  {A : Type} (mirror : Tree A -> Tree A) : Prop :=
    (forall t : Tree A, mirrorFG mirror t (mirror t)). (* /\
    (forall (x : A) (ts : list (Tree A))*)

(** Brak wywołania rekurencyjnego (explicite) to brak hipotezy
    indukcyjnej. *)
Goal
  forall {A : Type} (mirror : Tree A -> Tree A),
    mirror_spec mirror ->
      forall t : Tree A, mirror (mirror t) = t.
Proof.
  unfold mirror_spec. intros.
  specialize (H t). inversion H.
  rewrite H2.
Abort.

Module xd.

Fail Inductive mirrorFG
  {A : Type} (f : Tree A -> Tree A) : Tree A -> Tree A -> Prop :=
    | mirrorFG_0 :
        forall (x : A) (ts ts' : list (Tree A)),
          mirrorFGs f ts ts' ->
            mirrorFG f (Node x ts) (Node x (rev ts'))

with mirrorFGs (f : Tree A -> Tree A) : list (Tree A) -> list (Tree A) -> Prop := .

End xd.