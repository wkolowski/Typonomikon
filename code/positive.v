(** This piece of code was copied from
    https://vilhelms.github.io/posts/why-must-inductive-types-be-strictly-positive/
*)

Fail Inductive D : Type :=
  | D_intro : (D -> D) -> D.

Fail Inductive A : Type :=
  | introA : ((A -> Prop) -> Prop) -> A.

(* Section 3.1 from Thierry Coquand and Christine Paulin, 
   "Inductively defined types", COLOG-88. *)

(* Phi is a positive, but not strictly positive, operator. *)
Definition Phi (A : Type) := (A -> Prop) -> Prop.

Axioms
  (A : Type)
  (introA : Phi A -> A)
  (matchA : A -> Phi A)
  (beta : forall x, matchA (introA x) = x).

(* In particular, introA is an injection. *)
Lemma introA_injective :
  forall p p', introA p = introA p' -> p = p'.
Proof.
  intros.
  assert (matchA (introA p) = (matchA (introA p'))) as H1 by congruence.
  now repeat rewrite beta in H1.
Qed.

(* However, ... *) 

(* Proposition: For any type A, there cannot be an injection
   from Phi(A) to A. *)

(* For any type X, there is an injection from X to (X->Prop),
   which is λx.(λy.x=y) . *)
Definition i {A : Type} : A -> (A -> Prop) := 
  fun x y => x = y.

Lemma i_injective :
  forall (A : Type) (x y : A), i x = i y -> x = y.
Proof.
  intros.
  assert (i x x = i y x) as H1 by congruence.
  compute in H1.
  symmetry.
  rewrite <- H1.
  reflexivity.
Qed.

(* Hence, by composition, we get an injection f from A->Prop to A. *)
Definition f : (A -> Prop) -> A :=
  fun p => introA (i p).

Lemma f_injective :
  forall p p', f p = f p' -> p = p'.
Proof.
  unfold f. intros.
  apply introA_injective in H. apply i_injective in H. assumption.
Qed.

(* We are now back to the usual Cantor-Russel paradox. *)
(* We can define *)
Definition P0 : A -> Prop
  := fun x =>  exists (P : A -> Prop), f P = x /\ ~ P x.
  (* i.e., P0 x := x codes a set P such that x ∉ P. *)

Definition x0 := f P0.

(* We have (P0 x0) iff ~(P0 x0) *)
Lemma bad : (P0 x0) <-> ~(P0 x0).
Proof.
split.
  * intros [P [H1 H2]] H.
    change x0 with (f P0) in H1.
    apply f_injective in H1. rewrite H1 in H2.
    auto.
  * intros.
    exists P0. auto.
Qed.

(* Hence a contradiction. *)
Theorem worse : False.
Proof.
  pose bad. tauto.
Qed.