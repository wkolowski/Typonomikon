(** This piece of code was copied from
    https://vilhelms.github.io/posts/why-must-inductive-types-be-strictly-positive/
*)

(** TODO: ścisła pozytywność dla indeksowanych typów induktywnych. *)

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
  rewrite <- (beta p), <- (beta p'), H.
  reflexivity.
Qed.

(* For any type X, there is an injection from X to (X->Prop),
   which is λx.(λy.x=y) . *)
Definition i {A : Type} : A -> (A -> Prop) := 
  fun x y => x = y.

Lemma i_injective :
  forall (A : Type) (x y : A), i x = i y -> x = y.
Proof.
  unfold i. intros.
  apply (f_equal (fun f => f y)) in H.
  rewrite H. reflexivity.
Qed.

(* Hence, by composition, we get an injection f from A->Prop to A. *)
Definition f (P : A -> Prop) : A := introA (i P).

Lemma f_injective :
  forall P Q : A -> Prop, f P = f Q -> P = Q.
Proof.
  unfold f. intros.
  apply (f_equal matchA) in H.
  rewrite !beta in H.
  apply i_injective in H.
  assumption.
Qed.

Definition P : A -> Prop :=
  fun x : A =>  exists (P : A -> Prop), f P = x /\ ~ P x.

Definition x := f P.

Lemma bad : (P x) <-> ~ P x.
Proof.
split.
  * intros [P' [H1 H2]] H.
    change x with (f P) in H1.
    apply f_injective in H1. rewrite H1 in H2.
    auto.
  * intros.
    exists P. auto.
Qed.

(* Hence a contradiction. *)
Theorem worse : False.
Proof.
  pose bad. tauto.
Qed.