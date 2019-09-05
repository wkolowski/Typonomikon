(*
Definition Phi (A : Type) := (A -> bool) -> bool.

Axioms
  (A : Type)
  (introA : Phi A -> A)
  (matchA : A -> Phi A)
  (beta : forall x, matchA (introA x) = x).

Lemma introA_injective :
  forall x y : Phi A, introA x = introA y -> x = y.
Proof.
  intros.
  rewrite <- (beta x), <- (beta y), H.
  reflexivity.
Qed.

(*
Definition i {A : Type} : A -> (A -> bool) := 
  fun x y => x = y.

Lemma i_injective :
  forall (A : Type) (x y : A), i x = i y -> x = y.
Proof.
  unfold i. intros.
  apply (f_equal (fun f => f y)) in H.
  rewrite H. reflexivity.
Qed.
*)

Axioms
  (i : forall {A : Type}, A -> (A -> bool))
  (i_inj :
    forall (A : Type) (x y : A), i x = i y -> x = y).

Definition f (P : A -> bool) : A := introA (i P).

Lemma f_injective :
  forall P Q : A -> bool, f P = f Q -> P = Q.
Proof.
  unfold f. intros.
  apply (f_equal matchA) in H.
  rewrite !beta in H.
  apply i_inj in H.
  assumption.
Qed.

Definition P : A -> bool :=
  fun x : A => exists (P : A -> Prop), f P = x /\ ~ P x.

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
*)