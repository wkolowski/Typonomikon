Require Import List.
Import ListNotations.

Inductive Tree (A : Type) : Type :=
| Empty : Tree A
| Node : A -> list (Tree A) -> Tree A.

Arguments Empty {A}.
Arguments Node {A} _ _.

Require Import Recdef.

Fixpoint fmap {A B : Type} (f : A -> B) (t : Tree A) : Tree B :=
match t with
| Empty => Empty
| Node x ts => Node (f x) (map (fmap f) ts)
end.

Fail Functional Scheme fmap_ind := Induction for fmap Sort Prop.

Inductive R {A B : Type} (f : A -> B) : Tree A -> Tree B -> Prop :=
| R_Empty : R f Empty Empty
| R_Node  :
    forall (x : A) (ts : list (Tree A)) (ts' : list (Tree B)),
      Rs f ts ts' -> R f (Node x ts) (Node (f x) ts')

with
  Rs {A B : Type} (f : A -> B)
    : list (Tree A) -> list (Tree B) -> Prop :=
| Rs_nil  : Rs f [] []
| Rs_cons :
    forall
      (ta : Tree A) (tb : Tree B)
      (tsa : list (Tree A)) (tsb : list (Tree B)),
        R f ta tb -> Rs f tsa tsb -> Rs f (ta :: tsa) (tb :: tsb).

Fixpoint mirror {A : Type} (t : Tree A) : Tree A :=
match t with
| Empty => Empty
| Node x ts => Node x (rev (map mirror ts))
end.

Check Forall2.

Module v2.

Inductive R {A B : Type} (f : A -> B) : Tree A -> Tree B -> Prop :=
| R_Empty : R f Empty Empty
| R_Node  :
    forall (x : A) (ts : list (Tree A)) (ts' : list (Tree B)),
      Forall2 (R f) ts ts' -> R f (Node x ts) (Node (f x) ts').

Lemma correct :
  forall {A B : Type} (f : A -> B) (ta : Tree A) (tb : Tree B),
    R f ta tb -> fmap f ta = tb.
Proof.
  fix IH 6.
  destruct 1; cbn; [easy |].
  induction H; cbn; [easy |].
  do 2 f_equal.
  - now apply IH.
  - now congruence.
Defined.

Lemma complete :
  forall {A B : Type} (f : A -> B) (ta : Tree A) (tb : Tree B),
    fmap f ta = tb -> R f ta tb.
Proof.
  fix IH 4.
  destruct ta as [| a tas]; cbn; intros tb <-.
  - now constructor.
  - constructor.
    induction tas as [| ta tas' IH']; cbn.
    + now constructor.
    + constructor.
      * now apply IH.
      * easy.
Defined.

End v2.