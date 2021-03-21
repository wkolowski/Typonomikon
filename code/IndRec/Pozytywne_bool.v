(** Potencjalnie użyteczne linki:
    - https://cstheory.stackexchange.com/questions/14415/guarded-negative-occurrences-in-definition-of-inductive-types-always-bad
    - https://stackoverflow.com/questions/12651146/why-inductive-datatypes-forbid-types-like-data-bad-a-c-bad-a-a-where-th
*)

Unset Positivity Checking.
Inductive Pos : Type :=
    | Pos' : ((Pos -> bool) -> bool) -> Pos.
Set Positivity Checking.

Definition id {A : Type} : A -> A :=
  fun x : A => x.

Definition comp {A B C : Type} (f : A -> B) (g : B -> C) : A -> C :=
  fun x : A => g (f x).

Infix ".>" := comp (at level 50). 

Lemma comp_assoc :
  forall (A B C D : Type) (f : A -> B) (g : B -> C) (h : C -> D),
    (f .> g) .> h = f .> (g .> h).
Proof.
  reflexivity.
Qed.

Lemma comp_id_r :
  forall (A B : Type) (f : A -> B),
    f .> id = f.
Proof.
  reflexivity.
Qed.

Definition toProp (b : bool) : Prop :=
  b = true.

Axiom toBool : Prop -> bool.

Axiom toProp_toBool :
  forall P : Prop,
    toProp (toBool P) = P.

Axiom toProp_toBool' :
  toBool .> toProp = id.

Definition f (P : Pos -> Prop) : Pos :=
  Pos' (fun Q : Pos -> bool => toBool (P .> toBool = Q)).

Lemma injective_f :
  forall P Q : Pos -> Prop,
    f P = f Q -> P = Q.
Proof.
  inversion 1.
  apply (f_equal (fun f => toProp (f (Q .> toBool)))) in H1.
  rewrite 2!toProp_toBool in H1.
  cut (P .> toBool = Q .> toBool).
    intro. apply (f_equal (fun f => f .> toProp)) in H0.
      rewrite 2!comp_assoc, toProp_toBool', 2!comp_id_r in H0. assumption.
    rewrite H1. reflexivity.
Qed.

Definition wut (x : Pos) : Prop :=
  exists P : Pos -> Prop, f P = x /\ ~ P x.

Lemma paradox : wut (f wut) <-> ~ wut (f wut).
Proof.
  split.
    destruct 1 as (P & H1 & H2). intro H.
      apply injective_f in H1. subst. contradiction.
    intro H. red. exists wut. split.
      reflexivity.
      assumption.
Qed.

Theorem Pos_illegal : False.
Proof.
  pose paradox. firstorder.
Qed.